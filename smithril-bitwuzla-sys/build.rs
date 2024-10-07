use std::{env, fs};

use std::path::PathBuf;
use std::process::Command;
extern crate dirs;
extern crate pkg_config;

fn main() {
    let smithrill_install_path =
        env::var("SMITHRIL_INSTALL_PATH").unwrap_or(".smithril".to_string());
    let dir_smithril: PathBuf = dirs::home_dir().unwrap().join(smithrill_install_path);
    fs::create_dir_all(&dir_smithril).unwrap();
    let bitwuzla_version = "0.5.0";
    let folder_name = format!("bitwuzla-{}", bitwuzla_version);
    let dir_bitwuzla: PathBuf = dir_smithril.join(&folder_name);
    if !dir_bitwuzla.exists() {
        let mut _my_command = Command::new("git")
            .arg("clone")
            .arg("https://github.com/bitwuzla/bitwuzla.git")
            .arg(&folder_name)
            .current_dir(&dir_smithril)
            .status()
            .unwrap();
        let mut _my_command = Command::new("git")
            .arg("checkout")
            .arg(format!("tags/{}", bitwuzla_version))
            .arg("-b")
            .arg(format!("branch-{}", bitwuzla_version))
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

    let old_pkg_config_path = env::var("PKG_CONFIG_PATH");
    let pkg_config_dir: PathBuf = if cfg!(target_os = "macos") {
        dir_bitwuzla.join("build/install/lib/pkgconfig")
    } else {
        dir_bitwuzla.join("build/install/lib/x86_64-linux-gnu/pkgconfig")
    };

    let pkg_config_paths = vec![pkg_config_dir];
    let pkg_config_path = env::join_paths(pkg_config_paths).unwrap();
    env::set_var("PKG_CONFIG_PATH", pkg_config_path);

    let library = pkg_config::probe_library("bitwuzla").unwrap();

    env::set_var(
        "PKG_CONFIG_PATH",
        old_pkg_config_path.unwrap_or_else(|_| "".into()),
    );

    if cfg!(target_os = "macos") {
        println!("cargo:rustc-link-lib=c++");
    } else {
        println!("cargo:rustc-link-lib=stdc++");
    }

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
