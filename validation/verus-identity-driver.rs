#![feature(rustc_private)]

extern crate rust_verify;
extern crate serde_json;
extern crate vir;

use std::io::Write;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments: Vec<String> = std::env::args().collect();
    let verus_root = rust_verify::driver::find_verusroot().ok_or("missing pinned Verus root")?;
    if arguments.get(1).map(String::as_str) == Some(rust_verify::trait_check::TC_DRIVER_ARG) {
        let status = std::process::Command::new(verus_root.path.join("rust_verify"))
            .args(&arguments[1..])
            .status()?;
        std::process::exit(status.code().unwrap_or(2));
    }
    if std::env::var_os(rust_verify::cargo_verus::VERUS_DRIVER_VIA_CARGO).is_some() {
        return Err("direct compiler capture does not support Cargo wrapper mode".into());
    }
    let output = std::env::var("JPEG2000_NAMES_OUTPUT")?;
    let program = arguments.remove(0);
    let root = &verus_root.path;
    let version: serde_json::Value =
        serde_json::from_slice(&std::fs::read(root.join("version.json"))?)?;
    if version["verus"]["commit"] != "426d8b01e7ffb910a36c15e1f870ff985bb61eef" {
        return Err("unqualified Verus compiler commit".into());
    }
    let captured_arguments = arguments.clone();
    let vstd = Some((
        "vstd".to_owned(),
        root.join("vstd.vir").display().to_string(),
    ));
    let (args, rustc_args) =
        rust_verify::config::parse_args_with_imports(&program, arguments.into_iter(), vstd);
    std::env::set_var("RUSTC_BOOTSTRAP", "1");
    let verifier = rust_verify::verifier::Verifier::new(
        args,
        None,
        false,
        rust_verify::cargo_verus_dep_tracker::DepTracker::init(),
    );
    let (verifier, _, status) =
        rust_verify::driver::run(verifier, rustc_args, Some(verus_root), false);
    if status.is_err() || verifier.encountered_vir_error || verifier.count_errors != 0 {
        return Err("pinned driver verification failed".into());
    }
    let hints = verifier
        .erasure_hints
        .as_ref()
        .ok_or("missing actual erasure hints")?;
    let mut functions = Vec::new();
    for function in &hints.vir_crate.functions {
        let name = &function.x.name;
        functions.push(serde_json::json!({
            "canonical": serde_json::to_value(name)?,
            "compiler_result_label": vir::ast_util::fun_as_friendly_rust_name(name),
            "mode": format!("{:?}", function.x.mode),
            "span": function.span.as_string,
            "result_details": verifier.func_details.get(name).map(|details| details.to_json()),
        }));
    }
    let report = serde_json::json!({
        "format_version": 1,
        "scope": "Pinned compiler identity observations; not a qualified production denominator or native/Verus erasure correspondence.",
        "compiler_version": version,
        "arguments": captured_arguments,
        "source_function_coverage": "not-measured",
        "functional_coverage": "not-measured",
        "runtime_reachability": "not-measured",
        "verified": verifier.count_verified,
        "errors": verifier.count_errors,
        "entire_crate": rust_verify::driver::is_verifying_entire_crate(&verifier),
        "functions": functions,
        "resolved_erasure_calls": hints.resolved_calls.len(),
        "hir_vir_identity_pairs": hints.hir_vir_ids.len(),
    });
    let mut file = std::fs::OpenOptions::new()
        .create_new(true)
        .write(true)
        .open(output)?;
    file.write_all(&serde_json::to_vec_pretty(&report)?)?;
    Ok(())
}
