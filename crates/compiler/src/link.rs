use std::process::{self, Command};

#[allow(unused)]
enum Os {
    Linux,
    Windows,
    Osx,
}

#[cfg(target_os = "linux")]
const OS: Option<Os> = Some(Os::Linux);

#[cfg(target_os = "windows")]
const OS: Option<Os> = Some(Os::Windows);

#[cfg(target_os = "macos")]
const OS: Option<Os> = Some(Os::Osx);

#[cfg(not(any(target_os = "linux", target_os = "windows", target_os = "macos")))]
const OS: Option<Os> = None;

pub fn link(
    obj: &str,
    out: &str,
    linker_cmd: Option<&str>,
    linked_libraries: &[String],
) -> Result<(), String> {
    let mut cmd = if let Some(link) = &linker_cmd {
        let mut cmd = Command::new("eval");
        cmd.arg(link.replace("[OBJ]", obj).replace("[OUT]", out));
        cmd
    } else if let Some(cmd) = link_cmd(obj, out, linked_libraries) {
        cmd
    } else {
        return Err(format!(
            "No link command known for this OS. You can manually link the object file created: {obj}"
        ));
    };

    cmd.stdout(process::Stdio::piped());
    cmd.stderr(process::Stdio::piped());

    let proc = cmd.spawn().expect("Failed to spawn linker process");
    let output = proc.wait_with_output().expect("Linker process is invalid");

    output.status.success().then_some(()).ok_or_else(|| {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        format!(
            "The linker failed with the following output:\
            \n{}\n{}\n",
            stdout, stderr,
        )
    })
}

fn link_cmd(obj: &str, out: &str, link: &[String]) -> Option<Command> {
    let os = OS?;
    Some(match os {
        Os::Linux => {
            let mut cmd = Command::new("ld");
            cmd.args([
                obj,
                //"-dynamic-linker",
                //"/lib64/ld-linux-x86-64.so.2",
                "-lc",
                "help/linux/entry.o",
                "-o",
                out,
            ]);
            for lib in link {
                cmd.arg(format!("-l{lib}"));
            }
            cmd
        }
        Os::Windows => {
            // FIXME: don't hardcode the sdk path
            let msvc_path = r"C:\Program Files (x86)\Microsoft Visual Studio\2019\Community\VC\Tools\MSVC\14.29.30133";
            let sdk_path = r"C:\Program Files (x86)\Windows Kits\10\Lib\10.0.19041.0";
            let mut cmd = Command::new(format!(r#"{}\bin\Hostx64\x64\link.exe"#, msvc_path));
            cmd.args([
                "/NOLOGO",
                &format!(r#"/LIBPATH:{}\lib\x64"#, msvc_path),
                &format!(r#"/LIBPATH:{}\um\x64"#, sdk_path),
                &format!(r#"/LIBPATH:{}\ucrt\x64"#, sdk_path),
                obj,
                "kernel32.lib",
                "advapi32.lib",
                "userenv.lib",
                "ws2_32.lib",
                "bcrypt.lib",
                "msvcrt.lib",
                "legacy_stdio_definitions.lib",
                "/NXCOMPAT",
                &format!("/OUT:{out}"),
                "/OPT:REF,NOICF",
                "/DEBUG",
            ]);
            for lib in link {
                cmd.arg(lib);
            }
            cmd
        }
        Os::Osx => {
            let sdk_path_output = Command::new("xcrun")
                .args(["-sdk", "macosx", "--show-sdk-path"])
                .output()
                .expect("Failed to run command to find sdk path");
            let sdk_path = String::from_utf8(sdk_path_output.stdout)
                .expect("SDK path contains invalid characters. Can't link against system library");

            let mut cmd = Command::new("ld");
            cmd.args([
                obj,
                "-L/usr/local/lib",
                "-lSystem",
                "-syslibroot",
                sdk_path.trim(),
                "-o",
                out,
            ]);
            for lib in link {
                cmd.arg(format!("-l{lib}"));
            }
            cmd
        }
    })
}
