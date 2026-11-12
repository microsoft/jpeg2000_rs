#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_hir;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_span;

use rustc_driver::{Callbacks, Compilation};
use rustc_hir::def::{CtorKind, DefKind};
use rustc_interface::interface;
use rustc_middle::{
    mir::TerminatorKind,
    ty::{self, TyCtxt},
};
use serde_json::json;
use std::io::Write;
use std::path::PathBuf;

fn coordinates(
    tcx: TyCtxt<'_>,
    span: rustc_span::Span,
) -> (Option<String>, Option<[usize; 2]>, Option<[usize; 2]>) {
    if span.is_dummy() {
        return (None, None, None);
    }
    let source = tcx.sess.source_map();
    let begin = source.lookup_char_pos(span.lo());
    let end = source.lookup_char_pos(span.hi());
    (
        Some(begin.file.name.prefer_local_unconditionally().to_string()),
        Some([begin.line, begin.col.0]),
        Some([end.line, end.col.0]),
    )
}

struct Capture {
    crate_name: String,
    capture_id: String,
    output: PathBuf,
    arguments: Vec<String>,
}

impl Callbacks for Capture {
    fn after_analysis<'tcx>(
        &mut self,
        _compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> Compilation {
        if tcx.crate_name(rustc_hir::def_id::LOCAL_CRATE).as_str() != self.crate_name {
            return Compilation::Continue;
        }
        let body_owners: std::collections::HashSet<_> = tcx.hir_body_owners().collect();
        let mut functions = Vec::new();
        let mut other_body_owners = Vec::new();
        for local in tcx.iter_local_def_id() {
            let id = local.to_def_id();
            let kind = tcx.def_kind(id);
            if !matches!(
                kind,
                DefKind::Fn | DefKind::AssocFn | DefKind::Closure | DefKind::Ctor(..)
            ) {
                if body_owners.contains(&local) {
                    other_body_owners.push(json!({
                        "def_id": format!("{id:?}"),
                        "def_path": tcx.def_path_str(id),
                        "kind": format!("{kind:?}"),
                    }));
                }
                continue;
            }
            let span = tcx.def_span(id);
            let (source, begin, end) = coordinates(tcx, span);
            let implementation = tcx.impl_of_assoc(id);
            let runtime_callable = !matches!(kind, DefKind::Ctor(_, CtorKind::Const));
            let mir_available = tcx.is_mir_available(id);
            let mut calls = Vec::new();
            if runtime_callable && mir_available {
                let body = tcx.optimized_mir(local);
                for (block_index, block) in body.basic_blocks.iter_enumerated() {
                    let (call_source, call_begin, call_end) =
                        coordinates(tcx, block.terminator().source_info.span);
                    if let TerminatorKind::Call { func, .. } = &block.terminator().kind {
                        let called_type = func.ty(&body.local_decls, tcx);
                        let target = match called_type.kind() {
                            ty::FnDef(callee, arguments) => {
                                let resolution = match arguments.no_bound_vars() {
                                    None => json!({"dispatch": "unresolved-higher-ranked"}),
                                    Some(arguments) => match ty::Instance::try_resolve(
                                        tcx,
                                        ty::TypingEnv::post_analysis(tcx, local),
                                        *callee,
                                        arguments,
                                    ) {
                                        Ok(None) => json!({"dispatch": "unresolved-generic"}),
                                        Ok(Some(instance)) => {
                                            let dispatch = match instance.def {
                                                ty::InstanceKind::Item(_) => "item",
                                                ty::InstanceKind::Virtual(..) => "virtual",
                                                ty::InstanceKind::Intrinsic(_)
                                                | ty::InstanceKind::LlvmIntrinsic(_) => "intrinsic",
                                                ty::InstanceKind::Shim(_) => "shim",
                                            };
                                            json!({
                                                "dispatch": dispatch,
                                                "instance": format!("{:?}", instance.def),
                                                "def_id": format!("{:?}", instance.def_id()),
                                                "def_path": tcx.def_path_str(instance.def_id()),
                                                "generic_arguments": format!("{:?}", instance.args),
                                            })
                                        }
                                        Err(error) => fail(format!(
                                            "compiler instance resolution failed: {error:?}"
                                        )),
                                    },
                                };
                                json!({
                                    "kind": "compiler-fn-def",
                                    "def_id": format!("{callee:?}"),
                                    "def_path": tcx.def_path_str(*callee),
                                    "generic_arguments": format!("{arguments:?}"),
                                    "local": callee.is_local(),
                                    "trait_declaration": tcx.trait_of_assoc(*callee).map(|owner| tcx.def_path_str(owner)),
                                    "resolution": resolution,
                                })
                            }
                            ty::FnPtr(..) => json!({"kind": "indirect-function-pointer"}),
                            _ => json!({
                                "kind": "unresolved",
                                "type": format!("{called_type:?}"),
                            }),
                        };
                        let mut target = target;
                        target["block"] = json!(format!("{block_index:?}"));
                        target["source"] = json!(call_source);
                        target["begin"] = json!(call_begin);
                        target["end"] = json!(call_end);
                        calls.push(target);
                    } else if let TerminatorKind::Drop { place, .. } = &block.terminator().kind {
                        calls.push(json!({
                            "kind": "drop-terminator",
                            "type": format!("{:?}", place.ty(&body.local_decls, tcx).ty),
                            "resolution": {"dispatch": "unresolved-destructor"},
                            "block": format!("{block_index:?}"),
                            "source": call_source,
                            "begin": call_begin,
                            "end": call_end,
                        }));
                    }
                }
            }
            functions.push(json!({
                "def_id": format!("{id:?}"),
                "def_path": tcx.def_path_str(id),
                "def_path_hash": format!("{:?}", tcx.def_path_hash(id)),
                "kind": format!("{kind:?}"),
                "source": source,
                "begin": begin,
                "end": end,
                "from_expansion": span.from_expansion(),
                "body_owner": body_owners.contains(&local),
                "runtime_callable": runtime_callable,
                "mir_available": mir_available,
                "mir_observed": runtime_callable && mir_available,
                "compiler_visibility_public": tcx.visibility(id).is_public(),
                "impl_def_id": implementation.map(|owner| format!("{owner:?}")),
                "impl_self_type_unnormalized": implementation.map(|owner| format!("{:?}", tcx.type_of(owner).instantiate_identity())),
                "calls": calls,
            }));
        }
        functions.sort_by(|left, right| left["def_path"].as_str().cmp(&right["def_path"].as_str()));
        let report = json!({
            "format_version": 1,
            "capture_id": self.capture_id,
            "compiler_commit": env!("NATIVE_INVENTORY_COMPILER_COMMIT"),
            "compiler_host": env!("NATIVE_INVENTORY_COMPILER_HOST"),
            "scope": "Native compiler observations; no qualified coverage, runtime reachability, erasure or Verus-result correspondence claim.",
            "crate": self.crate_name,
            "arguments": self.arguments,
            "target": format!("{:?}", tcx.sess.opts.target_triple),
            "functions": functions,
            "other_body_owners": other_body_owners,
            "boundaries": [
                "Resolved instances distinguish static items, shims and virtual dispatch; unresolved generic/higher-ranked targets remain explicit.",
                "Drop terminators are recorded without inferring their destructor implementation.",
                "Indirect function pointers remain explicitly unresolved.",
                "Declared visibility is not effective public reexport reachability.",
                "Constant constructors and non-function body owners are recorded, not silently counted as runtime functions.",
                "These diagnostic compiler identities are not Verus identities or a qualified production denominator."
            ],
        });
        let bytes = serde_json::to_vec_pretty(&report)
            .unwrap_or_else(|error| fail(format!("cannot serialize native inventory: {error}")));
        let mut output = std::fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&self.output)
            .unwrap_or_else(|error| fail(format!("native inventory output must be new: {error}")));
        output
            .write_all(&bytes)
            .unwrap_or_else(|error| fail(format!("cannot write native inventory: {error}")));
        Compilation::Continue
    }
}

fn fail(message: impl std::fmt::Display) -> ! {
    eprintln!("native-inventory: {message}");
    std::process::exit(2);
}

fn main() {
    let arguments: Vec<_> = std::env::args().skip(1).collect();
    let mut capture = Capture {
        capture_id: std::env::var("JPEG2000_INVENTORY_CAPTURE_ID").unwrap_or_else(|error| {
            fail(format!(
                "JPEG2000_INVENTORY_CAPTURE_ID is required: {error}"
            ))
        }),
        crate_name: std::env::var("JPEG2000_INVENTORY_CRATE")
            .unwrap_or_else(|error| fail(format!("JPEG2000_INVENTORY_CRATE is required: {error}"))),
        output: std::env::var_os("JPEG2000_INVENTORY_OUTPUT")
            .map(PathBuf::from)
            .unwrap_or_else(|| fail("JPEG2000_INVENTORY_OUTPUT is required")),
        arguments: arguments.clone(),
    };
    rustc_driver::run_compiler(&arguments, &mut capture);
}
