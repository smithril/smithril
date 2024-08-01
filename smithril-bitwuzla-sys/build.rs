use std::{env, fs};

use std::path::PathBuf;
use std::process::Command;
extern crate dirs;
extern crate pkg_config;

fn main() {
    let dir_smithril: PathBuf = dirs::home_dir().unwrap().join(".smithril");
    fs::create_dir_all(&dir_smithril).unwrap();
    let dir_bitwuzla: PathBuf = dir_smithril.join("bitwuzla");
    if !dir_bitwuzla.exists() {
        let mut _my_command = Command::new("git")
            .arg("clone")
            .arg("https://github.com/bitwuzla/bitwuzla.git")
            .current_dir(&dir_smithril)
            .status()
            .unwrap();
        let mut _my_command = Command::new("git")
            .arg("checkout")
            .arg("tags/0.4.0")
            .arg("-b")
            .arg("branch-0.4.0")
            .current_dir(&dir_bitwuzla)
            .status()
            .unwrap();
    }
    if !dir_bitwuzla.join("build").exists() {
        let mut _my_command = Command::new("./configure.py")
            .arg(format!(
                "--prefix={}",
                dir_bitwuzla
                    .join("build/install")
                    .into_os_string()
                    .into_string()
                    .unwrap()
            ))
            .current_dir(&dir_bitwuzla)
            .status()
            .unwrap();

        let dir_tmp = dir_bitwuzla.join("build");
        let mut _my_command = Command::new("ninja")
            .arg("install")
            .current_dir(dir_tmp)
            .status()
            .unwrap();
    }

    let old = env::var("PKG_CONFIG_PATH");
    let pkg_config_dir: PathBuf = dir_bitwuzla.join("build/install/lib/x86_64-linux-gnu/pkgconfig");

    let paths = vec![pkg_config_dir];
    let paths = env::join_paths(paths).unwrap();
    env::set_var("PKG_CONFIG_PATH", paths);

    let library = pkg_config::probe_library("bitwuzla").unwrap();

    env::set_var("PKG_CONFIG_PATH", old.unwrap_or_else(|_| "".into()));

    println!("cargo:rustc-link-lib=stdc++");

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
