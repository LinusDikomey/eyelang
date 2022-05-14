use quote::quote;
use syn::DeriveInput;

#[proc_macro_derive(EnumSizeDebug)]
pub fn enum_size_debug(item: proc_macro::TokenStream) -> proc_macro::TokenStream {

    let input = syn::parse_macro_input!(item as DeriveInput);
    match input.data {
        syn::Data::Enum(enum_) => gen_enum_size(input.ident, enum_).into(),
        _ => panic!("Only enums are supported")
    }
}

fn gen_enum_size(ident: syn::Ident, input: syn::DataEnum) -> quote::__private::TokenStream {
    let variants = input.variants.iter().map(|variant| {
        let variant_name = &variant.ident;
        let msg = format!("\tSize of variant '{}': {{}}", variant_name);
        match &variant.fields {
            syn::Fields::Named(named) => {
                let fields = &named.named;
                quote! {
                    #[allow(dead_code)]
                    struct A{#fields}
                    println!(#msg, ::core::mem::size_of::<A>());
                }
            }
            syn::Fields::Unnamed(unnamed) => {
                let fields = &unnamed.unnamed;
                quote! {
                    #[allow(dead_code)]
                    struct A(#fields);
                    println!(#msg, ::core::mem::size_of::<A>());
                }
            }
            syn::Fields::Unit => quote! { println!(#msg, 0); },
        }
    });
    let start_msg = format!("---- Debugging sizes of enum '{ident}'. Overall: {{}}");
    let end_msg = format!("---- End of sizes of enum '{ident}'. Overall: {{}}");
    quote! {
        impl #ident {
            pub fn debug_sizes() {
                println!(#start_msg, ::core::mem::size_of::<Self>());
                #({ #variants })*
                println!(#end_msg, ::core::mem::size_of::<Self>());
            }
        }
    }
}