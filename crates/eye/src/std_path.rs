use std::path::PathBuf;

pub fn find() -> PathBuf {
    if let Some(path) = std::env::var_os("EYE_STD") {
        return path.into();
    }
    if let Some(path) = std::option_env!("EYE_DEFAULT_STD") {
        return path.into();
    }
    std::env::current_exe()
        .ok()
        .and_then(|path| path.parent().map(|path| path.join("std/")))
        .and_then(|std_path| {
            std_path
                .try_exists()
                .is_ok_and(|exists| exists)
                .then_some(std_path)
        })
        .unwrap_or(PathBuf::from("std/"))
}
