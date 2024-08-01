use std::path::PathBuf;
use std::process::{Command, ExitStatus};
use std::{env, fs, io};
extern crate dirs;
extern crate pkg_config;

fn build_z3(dir_z3: &PathBuf) -> io::Result<ExitStatus> {
    let mut _my_command = Command::new("mkdir")
        .arg("build")
        .current_dir(dir_z3)
        .status()?;
    let dir_tmp = dir_z3.join("build");
    _my_command = Command::new("cmake")
        .arg("-G")
        .arg("Ninja")
        .arg("-DCMAKE_BUILD_TYPE=Release")
        .arg(format!(
            "-DCMAKE_INSTALL_PREFIX={}",
            dir_tmp
                .join("install")
                .into_os_string()
                .into_string()
                .unwrap()
        ))
        .arg("../")
        .current_dir(&dir_tmp)
        .status()?;
    _my_command = Command::new("ninja")
        .arg("install")
        .current_dir(dir_tmp)
        .status()?;
    Ok(_my_command)
}

fn main() {
    let dir_smithril: PathBuf = dirs::home_dir().unwrap().join(".smithril");
    fs::create_dir_all(&dir_smithril).unwrap();
    let dir_z3: PathBuf = dir_smithril.join("z3");
    if !dir_z3.exists() {
        let mut _my_command = Command::new("git")
            .arg("clone")
            .arg("https://github.com/Z3Prover/z3.git")
            .current_dir(&dir_smithril)
            .status()
            .unwrap();
        let mut _my_command = Command::new("git")
            .arg("checkout")
            .arg("tags/z3-4.13.0")
            .arg("-b")
            .arg("branch-z3-4.13.0")
            .current_dir(&dir_z3)
            .status()
            .unwrap();
    }
    if !dir_z3.join("build").exists() {
        build_z3(&dir_z3).unwrap();
    }

    let old_ld_library_path = env::var("LD_LIBRARY_PATH");
    let ld_library_dir: PathBuf = dir_z3.join("build/install/lib");
    let ld_library_path = vec![ld_library_dir];
    let paths = env::join_paths(ld_library_path).unwrap();
    env::set_var("LD_LIBRARY_PATH", paths);

    let old_pkg_config_path = env::var("PKG_CONFIG_PATH");
    let pkg_config_dir: PathBuf = dir_z3.join("build/install/lib/pkgconfig");
    let pkg_config_path = vec![pkg_config_dir];
    let paths = env::join_paths(pkg_config_path).unwrap();
    env::set_var("PKG_CONFIG_PATH", paths);

    let library = pkg_config::probe_library("z3").unwrap();

    env::set_var(
        "PKG_CONFIG_PATH",
        old_pkg_config_path.unwrap_or_else(|_| "".into()),
    );
    env::set_var(
        "LD_LIBRARY_PATH",
        old_ld_library_path.unwrap_or_else(|_| "".into()),
    );

    let bindings = bindgen::builder()
        .header("wrapper.h")
        .clang_args(
            library
                .include_paths
                .iter()
                .map(|path| format!("-I{}", path.to_string_lossy())),
        )
        .prepend_enum_name(false)
        .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
        .generate()
        .expect("Unable to generate bindings");

    let out_path = PathBuf::from(env::var("OUT_DIR").unwrap());
    bindings
        .write_to_file(out_path.join("bindings.rs"))
        .expect("Couldn't write bindings!");

    println!("cargo::rerun-if-changed=build.rs");
}
