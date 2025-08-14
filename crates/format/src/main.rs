fn main() {
    for file in std::env::args().skip(1) {
        let contents = std::fs::read_to_string(&file)
            .unwrap_or_else(|err| panic!("Failed to open file {file}: {err:?}"));
        let formatted = format::format(contents.into_boxed_str());
        // TODO: write back the file when the formatter works properly
        eprintln!("Formatted {file}:\n{formatted}");
    }
}
