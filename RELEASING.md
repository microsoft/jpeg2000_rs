# Publishing and releasing

## Request publication from a release branch

The manually dispatched [Publish crate workflow](.github/workflows/release.yml)
follows the release process in
[`microsoft/jbig2_rs`](https://github.com/microsoft/jbig2_rs/blob/7b2f21ca82e595bc4353da6cd5fc5b5d571b4220/.github/workflows/release.yml).
Unlike its automatic release-event path, this workflow accepts **manual requests
only**: no push, tag, GitHub Release, or cron event uploads a crate.

The definition must be registered on the default branch for GitHub's Actions
UI, but **publication from `main` is forbidden**. In Actions, select
**Publish crate → Run workflow → Use workflow from `release/0.1`**
(or the matching `release/MAJOR.MINOR` branch). A request from `main`, a tag,
a fork, or a release line inconsistent with the version tag fails before
registry authentication. Both validation and publication retain that check.

Before using the workflow:

1. Review and deploy the same workflow, validation helpers and CI/proof push
   triggers to the intended release branch. The workflow-definition PR on
   `main` alone is not enough. Keep release-ref updates owner-controlled;
   this workflow never edits protections or promotes a source candidate.
2. Prepare and merge a separately authorized publication candidate on that
   release line. Its manifest must have the intended version and
   `publish = ["crates-io"]`; development and maintenance-source manifests
   remain disabled. No workflow patches `publish = false` in a dirty checkout.
3. Qualify both the reviewed PR head and exact integrated release commit.
   The core CI and Verus workflows now also run on `release/*` pushes.
   Their required native/MSRV, numerical, resource, package and proof gates
   must pass. Preserve the `packaged-verus-validation` artifact.
4. Create an explicitly approved immutable `vMAJOR.MINOR.PATCH` tag at that
   exact merged release-branch head, not a development tip, an older reachable
   tag, or an unmerged PR head. The dispatch SHA, reviewed integration and tag
   commit must be identical.
   Each job checks out the immutable dispatch SHA once and validates that
   checkout in place; neither workflow inputs nor helper outputs select a
   replacement checkout before running Cargo.
   This initial publisher accepts stable version tags, not prereleases.
5. A crate owner must configure crates.io Trusted Publishing for
   `microsoft/jpeg2000_rs`, workflow filename `release.yml`, environment
   `crates-io`. First configure that GitHub environment with release-owner
   approval and deployment branches restricted to the approved `release/*`
   lines. Merely naming an environment in YAML does **not** configure its
   protection rules. Use the repository's owner-review model without
   pretending that self-review is independent review.

After that setup and tag approval, request a credential-free rehearsal:

```sh
gh workflow run release.yml --repo microsoft/jpeg2000_rs --ref release/0.1 \
  -f tag=v0.1.1 -F dry_run=true
```

First request the tag with **`dry_run: true`** (the default).
No OIDC credentials are requested or registry uploads performed. Review the
source commit, CI producer identities and archive SHA256 in the validation
artifact. The action pins Python 3.13 (the release checker requires Python
3.11+; general validation retains its older supported Python profile).
Packaging uses Rust/Cargo **1.98.1**, matching the existing Verus
archive producer; it does not lower the runtime MSRV or change verifier pins.
The rebuilt archive must match the actual archive and input binding downloaded
from the successful, exact integrated-source Verus run—not merely similar
source files or an older preparation receipt. Expired/missing artifacts fail
closed and require requalification.

For a live request on the same release branch, explicitly set `dry_run: false`
and supply the owner-approved full `approved_commit` and `approved_sha256`
from that receipt. The protected publish job rechecks merged qualification,
the remote tag and exact rebuilt archive after approval, serializes uploads,
then obtains a short-lived crates.io OIDC token using a pinned action. The
token is scoped to the upload step and revoked by the authentication action.
No registry credentials belong in source, chat, logs, or workflow inputs.

An existing version is accepted only as an explicitly reported
`verified_existing_identical` registry result with matching checksum and
non-yanked state; it is not uploaded again. Any mismatch fails. After upload,
the workflow verifies the downloaded registry bytes and builds/runs a fresh
exact-version registry consumer under an isolated Cargo home.

Adding or merging this workflow does not authorize or perform a tag, upload,
release-branch update, or protection change. Publication remains an explicit
owner action for one version/source/archive. The experimental, non-certified
claims, disabled lifetime analysis, and source-function coverage limitations
are unchanged.

Publishing source, claiming standards conformance, and publishing a versioned
crate are different decisions. The development branch retains
`publish = false`; a versioned release candidate enables publication only
under its own exact authorization.

The registry package is `jpeg2000-decoder`, imported in Rust as
`jpeg2000_decoder`. Repository URLs remain `microsoft/jpeg2000_rs`.
Experimental [version 0.1.0](https://crates.io/crates/jpeg2000-decoder/0.1.0)
and bounded maintenance [version 0.1.1](https://crates.io/crates/jpeg2000-decoder/0.1.1)
are published. Confirm current ownership and appropriate token or publisher
permissions before preparing any subsequent version.

## Experimental 0.2 release preparation

The `release/0.2` decoder manifest is version 0.2.0 with
`publish = ["crates-io"]`; `main` advances separately to unpublished 0.3
development with publication disabled. This release includes
the newer PDF recovery/centered-output APIs and default-off deadline,
initial-MQ compatibility and buffered incremental profiles. None of those
additions is implied by installing the bounded 0.1.1 maintenance crate.
The default proof profile does not qualify the optional native coordinators;
all [profile boundaries](SUPPORTED.md#build-and-runtime-profiles) remain.

The initial zero-byte MQ case remains narrow, default-off compatibility, with
strict decoding unchanged. Its independent standards-validity investigation
remains [open](https://github.com/microsoft/jpeg2000_rs/issues/293); this
experimental release does not claim that question is resolved. Optional MQ,
deadline and incremental coordinators retain their native-only qualifications.

Release preparation does not approve an immutable tag or upload. Qualify the
reviewed candidate and actual integrated source/archive, then obtain the
separate exact tag and publication approvals described above. No tag,
workflow dispatch or upload follows merely from this manifest change.

## Published bounded maintenance 0.1.1

- Release branch: `release/0.1`; tag: `v0.1.1`.
- Exact source: `8562d6545742c2d6da18009edc4815605b4ac485`.
- Published archive SHA256:
  `c2a5c22a01937c6e212aeb4bc0a832e3ef06b746cf7d5b44a2ff2565cdfa7c35`.
- Operator publication workflow: `43866558872`, with exact registry checksum
  and fresh registry-consumer checks.

This contains the bounded compatible whole-packet-prefix correction, not the
newer full-main capabilities. Its source/archive receipts and the original
0.1.0 publication below retain their distinct identities.

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

### Image companion package

The source workspace also contains the separate
[`jpeg2000-image`](adapters/image/README.md) companion. It uses the workspace
decoder during development, whereas `cargo package -p jpeg2000-image --locked`
verifies against its declared registry dependency. The
[adapter workflow](.github/workflows/image-adapter.yml) tests both boundaries.
This does not replace the narrower unpacked-decoder probe above.

The companion retains `publish = false`; only the decoder's reviewed release
candidate permits crates.io publication. Adding the companion does not authorize
a registry name claim, version/tag, upload, or changes to the frozen release
branch. Any companion publication needs its own exact-candidate authorization,
including the decoder dependency version, package inventory, notices, supported
profile and platform results. Its code and tests are outside the decoder's
shipped package and Verus proof claim.

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
