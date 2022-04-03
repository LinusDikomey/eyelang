use std::process::{Command, Stdio};
use colored::Colorize;

use crate::Args;

#[allow(unused)]
enum Os {
    Linux,
    Windows,
    Osx
}

#[cfg(target_os = "linux")]
const OS: Option<Os> = Some(Os::Linux);

#[cfg(target_os = "windows")]
const OS: Option<Os> = Some(Os::Windows);

#[cfg(target_os = "macos")]
const OS: Option<Os> = Some(Os::Osx);

#[cfg(not(any(target_os = "linux", target_os = "windows", target_os = "macos")))]
const OS: Option<Os> = None;


pub fn link(obj: &str, out: &str, args: &Args) -> bool {
    let mut cmd = if let Some(link) = &args.link_cmd {
        let mut cmd = Command::new("eval");
        cmd.arg(link.replace("[OBJ]", obj).replace("[OUT]", out));
        cmd
    } else if let Some(cmd) = link_cmd(obj, out) {
            cmd
    } else {
        eprintln!("No link command known for this os. You can manually link the object file created: {obj}");
        return false;
    };

    cmd.stderr(Stdio::piped());

    let proc = cmd.spawn().expect("Failed to spawn linker process");
    let output = proc.wait_with_output().expect("Linker process is invalid");
    if !output.status.success() {
        let out = String::from_utf8_lossy(&output.stderr);
        eprintln!("{}:\n{out}", "Linking command failed with output".red());
        false
    } else { true }
}

fn link_cmd(obj: &str, out: &str) -> Option<Command> {
    let Some(os) = OS else { return None; };
    let mut cmd = Command::new(match os {
        Os::Linux | Os::Osx => "ld",
        Os::Windows => "link.exe",
    });
    cmd.arg(obj);
    cmd.arg("eyebuild/help.o");
    match os {
        Os::Linux => cmd.arg("-lc"),
        Os::Windows => todo!("Can't link automatically with windows yet. \
            You will have to link the object file in the eyebuild directory manually"),
        Os::Osx => {
            let sdk_path_output = Command::new("xcrun")
                .args(["-sdk", "macosx", "--show-sdk-path"])
                .output()
                .expect("Failed to run command to find sdk path");
            let sdk_path = String::from_utf8(sdk_path_output.stdout)
                .expect("SDK path contains invalid characters. Can't link against system library");

            cmd.args([
                "-L/usr/local/lib",
                "-lSystem",
                "-syslibroot",
            ]);
            cmd.arg(sdk_path.trim())
        }
    };
    cmd.args(["-o", out]);
    Some(cmd)
}