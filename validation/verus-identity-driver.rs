#![feature(rustc_private)]

extern crate rust_verify;
extern crate serde_json;
extern crate vir;

use std::io::Write;

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let mut arguments: Vec<String> = std::env::args().collect();
    let verus_root = rust_verify::driver::find_verusroot().ok_or("missing pinned Verus root")?;
    let version: serde_json::Value =
        serde_json::from_slice(&std::fs::read(verus_root.path.join("version.json"))?)?;
    if version["verus"]["commit"] != "426d8b01e7ffb910a36c15e1f870ff985bb61eef" {
        return Err("unqualified Verus compiler commit".into());
    }
    let target_crate = match std::env::var("JPEG2000_NAMES_CRATE") {
        Ok(name) if !name.trim().is_empty() => Some(name),
        Ok(_) => return Err("capture crate must not be empty".into()),
        Err(std::env::VarError::NotPresent) => None,
        Err(error) => return Err(error.into()),
    };
    let invocation_crate = arguments
        .windows(2)
        .find_map(|pair| (pair[0] == "--crate-name").then_some(pair[1].as_str()));
    if arguments.get(1).map(String::as_str) == Some(rust_verify::trait_check::TC_DRIVER_ARG)
        || arguments.iter().any(|arg| arg == "--version")
        || target_crate
            .as_deref()
            .zip(invocation_crate)
            .is_some_and(|(target, actual)| target != actual)
    {
        let executable = if arguments.get(1).map(String::as_str)
            == Some(rust_verify::trait_check::TC_DRIVER_ARG)
        {
            "rust_verify"
        } else {
            "verus"
        };
        let status = std::process::Command::new(verus_root.path.join(executable))
            .args(&arguments[1..])
            .status()?;
        std::process::exit(status.code().unwrap_or(2));
    }
    let output = std::env::var("JPEG2000_NAMES_OUTPUT")?;
    let program = arguments.remove(0);
    let root = &verus_root.path;
    let captured_arguments = arguments.clone();
    let mut dep_tracker = rust_verify::cargo_verus_dep_tracker::DepTracker::init();
    let via_cargo = dep_tracker.compare_env(rust_verify::cargo_verus::VERUS_DRIVER_VIA_CARGO, "1");
    if via_cargo {
        if target_crate.is_none() {
            return Err("Cargo capture requires JPEG2000_NAMES_CRATE".into());
        }
        if !arguments.first().is_some_and(|arg| arg.contains("rustc")) {
            return Err("Cargo invocation is missing its compiler argument".into());
        }
        arguments.remove(0);
        if rust_verify::cargo_verus::extend_args_and_check_is_direct_rustc_call(
            &mut arguments,
            &mut dep_tracker,
        ) {
            arguments.insert(0, program);
            rust_verify::driver::run_rustc_compiler_directly(&arguments);
            return Ok(());
        }
    }
    let cargo_args =
        via_cargo.then(|| rust_verify::config::parse_cargo_args(&program, &mut arguments));
    let vstd = (!via_cargo).then(|| {
        (
            "vstd".to_owned(),
            root.join("vstd.vir").display().to_string(),
        )
    });
    let (args, rustc_args) =
        rust_verify::config::parse_args_with_imports(&program, arguments.into_iter(), vstd);
    let cargo_compile = cargo_args
        .as_ref()
        .is_some_and(|args| rust_verify::cargo_verus::is_compile(args, &mut dep_tracker));
    std::env::set_var("RUSTC_BOOTSTRAP", "1");
    let verifier =
        rust_verify::verifier::Verifier::new(args, cargo_args, cargo_compile, dep_tracker);
    let (verifier, _, status) = rust_verify::driver::run(
        verifier,
        rustc_args,
        (!via_cargo).then_some(verus_root),
        via_cargo,
    );
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
    let mut labels = std::collections::BTreeMap::new();
    for identity in verifier.func_details.keys() {
        *labels
            .entry(vir::ast_util::fun_as_friendly_rust_name(identity))
            .or_insert(0_usize) += 1;
    }
    let mut result_identities = Vec::new();
    for (identity, details) in &verifier.func_details {
        let label = vir::ast_util::fun_as_friendly_rust_name(identity);
        let count = labels[&label];
        result_identities.push(serde_json::json!({
            "canonical": serde_json::to_value(identity)?,
            "compiler_result_label": label,
            "reported_label_canonical_count": count,
            "reported_label_disposition": if count == 1 {
                "unique-reported-label"
            } else {
                "shared-reported-label"
            },
            "mode": verifier.get_function_mode(identity).map(|mode| format!("{mode:?}")),
            "result_details": details.to_json(),
        }));
    }
    let report = serde_json::json!({
        "format_version": 1,
        "scope": "Pinned compiler identity observations; not a qualified production denominator or native/Verus erasure correspondence.",
        "compiler_version": version,
        "arguments": captured_arguments,
        "cargo_mode": via_cargo,
        "source_function_coverage": "not-measured",
        "functional_coverage": "not-measured",
        "runtime_reachability": "not-measured",
        "verified": verifier.count_verified,
        "errors": verifier.count_errors,
        "entire_crate": rust_verify::driver::is_verifying_entire_crate(&verifier),
        "functions": functions,
        "result_identities": result_identities,
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
