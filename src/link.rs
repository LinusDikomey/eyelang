use std::process::Command;

pub fn link(obj: &str, out: &str) -> bool {
    let proc = link_cmd(obj, out).spawn().expect("Failed to spawn linker process");
    let output = proc.wait_with_output().expect("Linker process is invalid");
    if !output.status.success() {
        let out = String::from_utf8_lossy(&output.stdout);
        eprintln!("Linking failed:\n{out}");
        false
    } else { true }
}

fn link_cmd(obj: &str, out: &str) -> Command {
    let mut cmd = Command::new("ld");
    cmd.args([
        obj,
        "-L/usr/local/lib",
        "-lSystem",
        "-syslibroot",
        "/Library/Developer/CommandLineTools/SDKs/MacOSX.sdk",
        "-o",
        out
    ]);
    cmd
}