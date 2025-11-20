use std::{collections::HashMap, path::PathBuf};

use parser::parse;

fn all_eye_files() -> impl Iterator<Item = PathBuf> {
    let eye = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../eye/")
        .canonicalize()
        .unwrap();
    let mut entries: Vec<_> = std::fs::read_dir(eye).unwrap().collect();
    std::iter::from_fn(move || {
        loop {
            let entry = entries.pop()?.unwrap();
            let path = entry.path();
            if entry.file_type().unwrap().is_dir() {
                entries.extend(std::fs::read_dir(path).unwrap());
            } else if path.extension().is_some_and(|ext| ext == "eye") {
                break Some(path);
            }
        }
    })
}

#[test]
fn ast_maintained_during_formatting() {
    for file in all_eye_files() {
        if !std::fs::exists(file.with_extension("out")).unwrap_or(false) {
            // don't try to format files that should error/don't have specific out files
            continue;
        }
        println!("Testing formating of {}", file.display());
        let src = std::fs::read_to_string(&file).unwrap().into_boxed_str();
        let (formatted, errors) = format::format(src.clone());
        let formatted = formatted.into_boxed_str();
        if !errors.errors.is_empty() {
            panic!("Eye file has unexpected errors");
        }
        let _ast = parser::parse::<()>(src, &mut error::Errors::new(), HashMap::default());
        let mut formatted_errors = error::Errors::new();
        let _formatted_ast =
            parse::<()>(formatted.clone(), &mut formatted_errors, HashMap::default());
        if !formatted_errors.errors.is_empty() {
            panic!(
                "File {} had errors after formatting:\n{formatted}",
                file.display()
            );
        }
        // TODO: enable this assertion when ast equality is implemented
        // assert_eq!(
        //     ast,
        //     formatted_ast,
        //     "AST changed from formatting for file {}:\n{formatted}",
        //     file.display()
        // );
    }
}
