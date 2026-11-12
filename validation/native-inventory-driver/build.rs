use std::process::Command;

fn main() {
    let rustc = std::env::var_os("RUSTC").expect("Cargo must provide RUSTC");
    let version = Command::new(&rustc)
        .arg("-vV")
        .output()
        .expect("query compiler identity");
    assert!(version.status.success(), "compiler identity query failed");
    let version = String::from_utf8(version.stdout).expect("compiler identity must be UTF-8");
    let commit = version
        .lines()
        .find_map(|line| line.strip_prefix("commit-hash: "))
        .expect("compiler commit identity is missing");
    assert_eq!(
        commit, "11177f2235f0c842b00f82c558ad9480c0c3a895",
        "unqualified diagnostic compiler"
    );
    let host = version
        .lines()
        .find_map(|line| line.strip_prefix("host: "))
        .expect("compiler host identity is missing");
    let root = Command::new(&rustc)
        .args(["--print", "sysroot"])
        .output()
        .expect("query compiler sysroot");
    assert!(root.status.success(), "compiler sysroot query failed");
    let root = String::from_utf8(root.stdout).expect("compiler sysroot must be UTF-8");
    let root = root.trim_end();
    println!("cargo:rustc-env=NATIVE_INVENTORY_COMPILER_COMMIT={commit}");
    println!("cargo:rustc-env=NATIVE_INVENTORY_COMPILER_HOST={host}");
    println!("cargo:rustc-link-search=native={root}/lib");
    if cfg!(target_family = "unix") {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{root}/lib");
        println!("cargo:rustc-link-arg=-Wl,-rpath,{root}/lib/rustlib/{host}/lib");
    }
    println!("cargo:rerun-if-env-changed=RUSTC");
}
