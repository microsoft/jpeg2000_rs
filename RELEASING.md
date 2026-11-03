# Publishing and releasing

Publishing source, claiming standards conformance, and publishing a versioned
crate are different decisions. The development branch retains
`publish = false`; a versioned release candidate enables publication only
under its own exact authorization.

The registry package is `jpeg2000-decoder`, imported in Rust as
`jpeg2000_decoder`. Repository URLs remain `microsoft/jpeg2000_rs`.
Experimental [version 0.1.0](https://crates.io/crates/jpeg2000-decoder/0.1.0)
has been published manually. Confirm current ownership and appropriate token
or publisher permissions before preparing any subsequent version.

## Published experimental baseline

- Release branch: `release/0.1`.
- Exact source commit: `88b592261540cf6b951c89a61be408fbd2cf8367`.
- Published `jpeg2000-decoder-0.1.0.crate` SHA256:
  `5aaa9ebd893f174ee4f8278e319a43a123f754ce0249c5e76698ceda513f5a78`.
- [Versioned API documentation](https://docs.rs/jpeg2000-decoder/0.1.0/jpeg2000_decoder/).

This records a completed publication, not normative conformance, full Verus
coverage, or permission to repeat its one-use release operations.
The published version cannot be overwritten. Confirmed bounded corrections
to advertised behavior are considered for separately qualified 0.1.x
backports; unavoidable public API/data-model changes or new capabilities
belong in 0.2 under the [current release plan](https://github.com/microsoft/jpeg2000_rs/issues/226).
Executing code, mathematical models and regression tests must travel together.
The release branch remains frozen until an exact update is separately approved;
no new tag or upload follows merely from a documentation or development change.

The first manual upload did not require a GitHub publisher workflow. A
packaging dry-run helper is not a publisher, and future upload automation
requires its own ownership, authentication, protected environment, exact
source/archive qualification and review decisions.

## Source publication

- Confirm the approved source license and preserve required third-party notices.
- Review the exact source candidate, reachable Git history, repository metadata,
  and CI artifacts for restricted or internal-only material.
- Keep specifications, proofs, tests, reusable validation tooling, and relevant
  documentation in the source tree.
- Keep internal approval correspondence and generated run reports outside it.
- Keep maintained JSON manifests, schemas and the technical reference
  inventory under [validation/](validation/). They are test inputs, not
  disposable tracking files. Keep execution plans and task status in the
  issue/PR system rather than adding source-tree progress ledgers.
- Run the [contributor checks](CONTRIBUTING.md) from a clean clone.
- Describe the implemented profile and [proof boundaries](PROOFS.md) accurately.

Do not assume that removing a file from the current tree removes it from Git
history. An exported source snapshot and a visibility change on an existing
repository have different disclosure boundaries.

### Existing repository history and metadata

The owner must explicitly choose whether to retain reviewed history or approve
an exact cleanup plan before changing visibility. Closing pull requests,
deleting branches, or rewriting branch history does not by itself remove
GitHub-maintained PR refs, cached views, conversations, Actions logs, or artifacts.

GitHub marks PR refs as read-only. Its
[documented history-removal process](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/removing-sensitive-data-from-a-repository)
also states that Support does not remove non-sensitive data through that
process. Do not promise complete removal of ordinary development records on
that basis. Check the applicable platform process and remaining disclosure
boundary before proposing any destructive operation.

Source-publication approval does not by itself choose a history strategy or
authorize ref deletion, force-pushing, or repository replacement/renaming.
The repository is already public. Any future visibility, history or disclosure
operation still requires approval of its actual retained content and exact
scope; existing public visibility is not permission to disclose restricted
material or rewrite refs.

### Unsafe-code review

Confirm the library crate-level prohibition and the main, standalone fuzz and
image consumer packages' `unsafe_code = "forbid"` lints remain enabled. Review all owned
Rust targets, not only the default library configuration, and run their
compiler/Clippy checks. The current owned sources have no unsafe code to
replace; do not describe dependency or standard-library internals as audited
by that fact. A future change in this boundary requires a new review.

### Candidate checks

Use the same committed candidate for the [CI workflow](.github/workflows/ci.yml),
the [proof workflow](.github/workflows/verus.yml), and retained validation
artifacts. Follow the [contributor setup](CONTRIBUTING.md) for tool prerequisites.

| Gate | Required check |
|---|---|
| Rust behavior | All-target tests, doctests and release checks on supported platforms |
| Rust diagnostics | Formatting, strict Clippy and rustdoc |
| Packaged decoder | Exact package-file inventory, `cargo package --locked` with its verification build, and pinned formatting of the actual unpacked archive |
| External consumer | Standalone `image` adapter tests/doctest and release check on Rust 1.88, pinned formatting, strict Clippy and rustdoc against the unpacked package |
| General decoder validation | Python regression suite and `python validation/run-validation.py all` |
| Independent HT validation | Separate `python validation/run-validation.py htj2k` invocation |
| Representative process bounds | Separate Linux `python validation/run-validation.py resources` invocation |
| Expressed proof obligations | Exact production-root command and strict coverage checker from [PROOFS.md](PROOFS.md) |

The `all` command does not implicitly run the HT or resource gates. Passing a
package-file comparison also does not show that the packaged source compiles;
keep the package verification build enabled. `cargo package` is a local build
operation, not package-publication authorization.

Perform these checks in a clean checkout, regenerate the corpus without
changing tracked source, and retain source/tool/input/output hash bindings.
Keep skipped comparisons and unavailable external conformance inputs visible
rather than presenting them as passed checks.

### External `image` consumer exercise

The repository-only [consumer probe](validation/image-consumer-probe/src/lib.rs)
uses published `image` 0.25.10 with its built-in codecs disabled. Its dependency
points to the actual `cargo package` output, not the repository decoder.
The [CI quality job](.github/workflows/ci.yml) builds that package before running
the probe. Neither the probe nor `image` is added to the decoder's shipped
package or default dependency graph.

The probe implements `ImageDecoder` plus opt-in `ImageReader` hooks for a bounded
opaque grayscale/sRGB JP2 profile. Pixel decoding is deferred until the trait's
read method; strict `image` dimensions are checked first, and the original codec
resource limits remain in force. It is not streaming, comprehensive metadata or
profile support, a global memory bound, an upstream `image` integration, or part
of the decoder's Verus proof claim. Synthetic fixtures exercise API behavior,
not official conformance.

## Conformance evidence

- Reconcile the selected standards editions with the specification inventory.
- Execute all applicable authorized official vectors from external storage.
- Require bit-exact lossless output and measured, explicit lossy tolerances.
- Run independent decoder comparisons; preserve and adjudicate disagreements.
- Complete instrumented fuzz/resource campaigns for the claimed profile.
- Bind results to the source commit, input and oracle hashes, toolchain, solver,
  commands, and platform. Store results as release/CI artifacts.

Generated tests and successful Verus verification do not replace official
conformance testing. Missing inputs, skipped oracles, and untested platforms
must remain visible.

## Versioned package release

- Obtain owner authorization for a specific candidate and release scope.
- Confirm package contents, license metadata, examples, and API documentation.
- Verify Cargo metadata reports package `jpeg2000-decoder` and library target
  `jpeg2000_decoder`; exercise the actual `jpeg2000-decoder-<version>.crate`
  archive and its unpacked directory, not an old-name package left in `target`.
- Run the pinned formatter on the unpacked package as well as the repository,
  so conditional module paths do not point to omitted source files. Build and
  run the unpacked unit tests and doctests at the runtime minimum.
- Require the archive's separate whole-crate Verus replay and fail-closed
  collection, with unchanged input bindings; do not infer it from repository
  verification or source-file inclusion.
- Verify that ghost code is erased in ordinary Rust builds.
- Review all required validation and proof results against the same candidate.
- Set a version and enable package publication only when authorized.
- Verify the published source/package and its reproducible build commands.
