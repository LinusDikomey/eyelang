use crate::{
    ast::{self, ModuleId, Definition, ExprRef, Ast, TypeDef, FunctionId, TypeId},
    error::{Errors, Error},
    dmap::DHashMap,
    span::Span,
    parser::IdentId,
    resolve::types::ResolvedFunc,
    types::Primitive
};

use self::{
    types::{DefId, Type, SymbolTable, FunctionHeader, Struct, ResolvedTypeDef, Enum},
    type_info::{TypeTableIndex, TypeTable, TypeInfo, TypeTableIndices, TypeInfoOrIndex}, scope::{ModuleCtx, Scope, ExprInfo}
};

pub mod const_val;
mod scope;
mod cross_resolve;
pub mod types;
pub mod type_info;
mod expr;
mod pat;
mod exhaust;

pub fn resolve_project(ast: &Ast, main_module: ModuleId, errors: &mut Errors, require_main: bool)
-> (SymbolTable, Option<FunctionId>) {
    let mut symbols = SymbolTable::new(ast.functions.len(), ast.expr_count(), &ast.types, ast.traits.len(), ast.calls.len());

    // Add ids for definitions. Definitions that will have to be cross-resolved (use, const) are left as Unresolved
    let mut module_scopes: Vec<_> = ast.modules.iter().enumerate().map(|(i, module)| {
        let module_id = ModuleId::new(i as _);
        let module_ctx = ModuleCtx { src: ast.src(module_id).0, id: module_id, root: module.root_module };
        let names = scope_defs(&ast[module.definitions]);
        Scope::root(names, module_ctx)
    }).collect();   
    
    // set scope pointers
    let module_scopes_ptr: *const [Scope] = module_scopes.as_slice();
    for scope in &mut module_scopes {
        scope.set_module_scopes_ptr(module_scopes_ptr);
    }

    // resolve cross-referencing defs: use statements, constants (all DefId::Unresolved)
    cross_resolve::top_level(&mut module_scopes, ast, errors);
    
    // resolve types, function signatures
    for (module, scope) in ast.modules.iter().zip(&mut module_scopes) {
        for (name, def) in &ast[module.definitions] {
            resolve_def(name, def, ast, &mut symbols, scope, errors);
        }
    }

    let main = require_main.then_some(()).and_then(|()| {
        if let Some(DefId::Function(id)) = module_scopes[main_module.idx()].get_def("main") {
            let main = symbols.get_func(id);
            if main.varargs || main.params.len() != 0 {
                errors.emit_span(Error::MainArgs, ast.functions[id.idx()].span.in_mod(main_module));
            }
            match main.return_type {
                Type::Prim(p) if p.is_int() => {}
                Type::Prim(Primitive::Unit) => {}
                _ => errors.emit_span(
                    Error::InvalidMainReturnType("TODO: show type here".to_owned()),
                    ast.functions[id.idx()].return_type.span().in_mod(main_module)
                )
            }
            Some(id)
        } else {
            errors.emit_span(Error::MissingMain, Span::new(0, 0, main_module));
            None
        }
    });

    // function bodies
    debug_assert_eq!(ast.modules.len(), module_scopes.len());
    for (module, scope) in ast.modules.iter().zip(&module_scopes) {
        scope_bodies(scope, &ast[module.definitions], &ast, &mut symbols, errors);
    }

    (symbols, main)
}

/// add all order independent definitions to a scope
fn scope_defs<'a>(defs: &'a DHashMap<String, Definition>,) -> DHashMap<String, DefId> {
    defs.iter().map(|(name, def)| {
        let def_id = match def {
            &Definition::Function(id) => DefId::Function(id),
            &Definition::Type(id) => DefId::Type(id),
            &Definition::Trait(id) => DefId::Trait(id),
            &Definition::Module(id) => DefId::Module(id),
            Definition::Use(_) | Definition::Const(_, _) => DefId::Unresolved { resolving: false }, // added later
            &Definition::Global(id) => DefId::Global(id),
        };
        (name.clone(), def_id)
    }).collect()
}

fn scope_bodies(scope: &Scope, defs: &DHashMap<String, Definition>, ast: &Ast, symbols: &mut SymbolTable, errors: &mut Errors) {

    fn gen_func_body(id: FunctionId, scope: &Scope, generics_ctx: &[String], ast: &Ast, symbols: &mut SymbolTable, errors: &mut Errors) {
        let mut expr_types = vec![TypeTableIndex::NONE; ast.expr_count()];

        let func = &ast[id];
        if let Some(body) = func.body {
            let generic_count = symbols.get_func(id).generic_count();
        
            let mut types = TypeTable::new(generic_count);
            let mut vars = vec![];
            let mut idents = vec![Ident::Invalid; func.ident_count as usize];
            func_body(body, id, scope, generics_ctx, Ctx {
                ast,
                symbols,
                types: &mut types,
                idents: &mut idents,
                vars: &mut vars,
                errors,
                expr_types: &mut expr_types,
            });

            symbols.get_func_mut(id).resolved_body = Some(ResolvedFunc {
                body,
                idents,
                vars,
                types,
            })
        }
    }

    for (_name, def) in defs {
        match def {
            Definition::Function(func_id) => gen_func_body(*func_id, scope, &[], ast, symbols, errors),
            Definition::Type(id) => {
                match symbols.get_type(*id) {
                    ResolvedTypeDef::Struct(def) => {
                        // PERF: cloning generics here
                        let generics = def.generics.clone();
                        // PERF: collecting here (ownership reasons)
                        for method_id in def.methods.values().copied().collect::<Vec<_>>() {
                            gen_func_body(method_id, scope, &generics, ast, symbols, errors);
                        }
                        
                    }
                    ResolvedTypeDef::Enum(_) => {}
                    ResolvedTypeDef::NotGenerated { .. } => unreachable!(),
                }
                
            }
            Definition::Trait(_) | Definition::Module(_) | Definition::Use(_)
            | Definition::Const(_, _) | Definition::Global(_) => {}
        }
    }
}

fn resolve_def(name: &str, def: &Definition, ast: &Ast, symbols: &mut SymbolTable, scope: &mut Scope, errors: &mut Errors) {
    match def {
        &Definition::Function(id) => {
            symbols.place_func(id, func_signature(name.to_owned(), 0, &ast[id], scope, symbols, errors));
        }
        &Definition::Type(id) => {
            let def = match &ast[id] {
                TypeDef::Struct(s) => ResolvedTypeDef::Struct(struct_def(name.to_owned(), s, scope, ast, symbols, errors)),
                TypeDef::Enum(e) => ResolvedTypeDef::Enum(enum_def(name.to_owned(), e, scope, symbols, errors)),
            };
            symbols.place_type(id, def);
        }
        Definition::Trait(_)
        | Definition::Module(_)
        | Definition::Use(_)
        | Definition::Const(_, _) => {}
        Definition::Global(_) => todo!(),
    }
}

fn func_signature(name: String, inherited_generics_count: u8, func: &ast::Function, scope: &Scope, symbols: &SymbolTable, errors: &mut Errors)
-> FunctionHeader {
    let generics: Vec<String> = func.generics.iter().map(|span| scope.module.src()[span.range()].to_owned()).collect();
    let generic_defs = generics
        .iter()
        .enumerate()
        .map(|(i, name)| (name.clone(), DefId::Generic(i as u8)))
        .collect();
    let scope = scope.signature_scope(generic_defs);

    let params = func.params.iter().map(|(name, ty, _, _)| {
        (name.clone(), scope.resolve_ty(ty, symbols, errors))
    }).collect();

    let return_type = scope.resolve_ty(&func.return_type, symbols, errors);

    FunctionHeader {
        name,
        inherited_generic_count: inherited_generics_count,
        generics,
        params,
        return_type,
        varargs: func.varargs,
        resolved_body: None,
        module: scope.module.id,
    }
}

fn struct_def(name: String, def: &ast::StructDefinition, scope: &mut Scope, ast: &Ast, symbols: &mut SymbolTable, errors: &mut Errors)
-> Struct {    
    let names = def.generics.iter().enumerate().map(|(i, name_span)| {
        let name = &ast.src(scope.module.id).0[name_span.range()];
        (name.to_owned(), DefId::Generic(i as u8))
    }).collect();

    let scope = scope.child_scope(names);
    
    let members = def.members.iter().map(|(name, ty, _, _)| {
        (name.clone(), scope.resolve_ty(ty, symbols, errors))
    }).collect();

    let symbols = def.methods.iter().map(|(name, id)| {
        symbols.place_func(*id, func_signature(name.to_owned(), def.generic_count(), &ast[*id], &scope, symbols, errors));
        (name.clone(), *id)
    }).collect();

    let generics = def.generics.iter().map(|name_span| ast.src(scope.module.id).0[name_span.range()].to_owned()).collect();

    Struct {
        name,
        members,
        methods: symbols,
        generics,
    }
}

fn enum_def(name: String, def: &ast::EnumDefinition, _scope: &mut Scope, _symbols: &SymbolTable, _errors: &mut Errors)
-> Enum {
    let variants = def.variants.iter().enumerate().map(|(i, (_, name))| (name.clone(), i as _)).collect();
    Enum { name, variants, generic_count: def.generic_count() }
}

#[derive(Clone, Copy, Debug)]
pub enum Ident {
    Invalid,
    Var(VarId),
}

#[derive(Clone, Copy, Debug)]
pub struct VarId(u32);
impl VarId {
    pub fn idx(self) -> usize {
        self.0 as usize
    }
}

#[derive(Clone, Copy, Debug)]
pub struct Var {
    ty: TypeTableIndex,
}

struct Ctx<'a> {
    ast: &'a Ast,
    symbols: &'a mut SymbolTable,
    types: &'a mut TypeTable,
    idents: &'a mut [Ident],
    vars: &'a mut Vec<Var>,
    errors: &'a mut Errors,
    expr_types: &'a mut [TypeTableIndex],
}
impl<'a> Ctx<'a> {
    fn reborrow(&mut self) -> Ctx<'_> {
        Ctx {
            ast: self.ast,
            symbols: &mut *self.symbols,
            types: &mut *self.types,
            idents: &mut *self.idents,
            vars: &mut *self.vars,
            errors: &mut *self.errors,
            expr_types: &mut *self.expr_types,
        }
    }
    fn new_var(&mut self, var: Var) -> VarId {
        self.vars.push(var);
        VarId((self.vars.len() - 1) as _)
    }
    fn var(&self, id: VarId) -> Var {
        self.vars[id.0 as usize]
    }
    fn set_ident(&mut self, id: IdentId, ident: Ident) {
        self.idents[id.idx()] = ident;
    }
    fn ident(&self, id: IdentId) -> Ident {
        self.idents[id.idx()]
    }
    fn merge(&mut self, a: TypeTableIndex, b: TypeTableIndex, span: Span) {
        self.types.merge(a, b, self.errors, span, self.symbols);
    } 
    fn specify(&mut self, idx: TypeTableIndex, info: TypeInfo, span: Span) {
        self.types.specify(idx, info, self.errors, span, self.symbols)
    }
    
    pub fn specify_enum_variant(&mut self, idx: TypeTableIndex, name: &str, name_span: Span) {
        // avoid creating enum TypeInfo unnecessarily to avoid allocations and complex comparisons
        let (idx, ty) = self.types.find_optimizing(idx);
        match ty {
            TypeInfo::Enum(names) => {
                if !self.types.get_names(names).iter().any(|s| *s == name) {
                    let new_names = self.types.extend_names(names, std::iter::once(name.to_owned()));
                    self.types.update_type(idx, TypeInfo::Enum(new_names));
                }
            }
            TypeInfo::Resolved(id, _generics) => {
                if let ResolvedTypeDef::Enum(def) = self.symbols.get_type(id) {
                    if def.variants.get(name).is_none() {
                        self.errors.emit_span(Error::NonexistantEnumVariant, name_span);
                    }
                } else {
                    self.errors.emit_span(Error::MismatchedType {
                        expected: "an enum".to_string(), found: "a non-enum type".to_owned()
                    }, name_span);
                }
            }
            _ => {
                let variant = self.types.add_names(std::iter::once(name.to_owned()));
                self.specify(
                    idx,
                    TypeInfo::Enum(variant),
                    name_span,
                );
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum ResolvedCall {
    Function { func_id: FunctionId, generics: TypeTableIndices },
    Struct { type_id: TypeId, generics: TypeTableIndices },
    Invalid,
}

fn func_body<'a>(body: ExprRef, func_id: FunctionId, scope: &'a Scope<'a>, generics_ctx: &[String], ctx: Ctx) {
    let mut scope = scope.child();
    let signature = ctx.symbols.get_func(func_id);
    
    let generics = ctx.types.generics();
    let mut generic_types = generics.iter();

    for name in generics_ctx {
        let ty = generic_types.next().unwrap();
        scope.add_generic(name.clone(), ty);
    }
    for name in &signature.generics {
        let ty = generic_types.next().unwrap();
        scope.add_generic(name.clone(), ty);
    }

    let on_generic = |i| TypeInfoOrIndex::Idx(generics.nth(i as usize));

    for (i, (name, ty)) in signature.params.iter().enumerate() {
        let ty = ty.as_info(ctx.types, on_generic);
        let ty = ctx.types.add_info_or_idx(ty);
        ctx.vars.push(Var { ty });
        let var_id = VarId((ctx.vars.len() - 1) as _);
        ctx.idents[i] = Ident::Var(var_id);
        scope.define_var(name.clone(), var_id);
    }

    let signature = ctx.symbols.get_func(func_id);
    let return_type_info = signature.return_type.as_info(ctx.types, on_generic);
    let expected = ctx.types.add_info_or_idx(return_type_info);

    let mut noreturn = false;
    scope.val_expr(body, ExprInfo { expected, ret: expected, noreturn: &mut noreturn }, ctx, false);
}