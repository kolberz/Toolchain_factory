# Toolchain Factory

Toolchain Factory builds a genuine, portable Linux x86-64 Lean 4 + Lake + Mathlib environment on a GitHub-hosted Ubuntu runner. The browser application is an evidence viewer; it does not pretend to download artifacts, run Lean, or assign certification predicates.

## Exact toolchain profiles

The factory does not mix Lean versions or reuse compiled Mathlib artifacts
across versions. Each build selects one complete, allow-listed profile from
`toolchain-profiles.json`:

| Profile | Lean + Mathlib | Mathlib commit | Lean archive SHA-256 |
| --- | --- | --- | --- |
| `lean-4.32.2` (default) | `v4.32.2` | `905b95818eb32af7874a58b427f50c1711a5e96c` | `5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa` |
| `lean-4.33.0-rc1` | `v4.33.0-rc1` | `79d0395a1825a6264ad5d269e35e60537518955e` | `25e7b3e18ec75a4e2529fc23194be8e3cc3183df99b553f870d8a111c7488210` |

The rc1 profile exists for projects already pinned to
`leanprover/lean4:v4.33.0-rc1`; it is a separate toolchain, not a claim that
4.33 compiled artifacts are backward-compatible with 4.32. The certified
4.32.2 release remains immutable.

The workflow downloads the selected official release, verifies both its full
64-character SHA-256 and exact size, clones the exactly matching Mathlib tag,
verifies the resolved commit, `lean-toolchain`, and release lockfile, runs
`lake update`, and obtains Mathlib's compiled cache with `lake exe cache get`.
Because dependency default branches can move after a release, the workflow
restores and verifies the release's content-addressed `lake-manifest.json`
after the required `lake update`, then fetches/builds that locked dependency
graph.

## Certification model

The final predicate is:

```text
C_final = P AND T AND E AND O_1 AND O_2 AND R
```

- `P`: `profileId` selects one complete canonical profile, and every release, toolchain, Mathlib, lockfile, and architecture anchor matches that profile. Mixed-version anchors are rejected.
- `T`: every generated archive part has a valid SHA-256, checksum verification exits zero, the reassembled archive hash matches, and every part is strictly smaller than 450 MiB.
- `E`: the workflow executes the server-owned gates with their expected outcomes. Positive gates must exit zero; the deliberately invalid theorem must exit nonzero.
- `O_1` and `O_2`: two separate extraction roots reproduce the packaged tree hash and run `lake build` plus `lake env lean MathlibSmoke.lean` in separate Docker containers using `--network none`. The verifier image and its Git executable are prepared before isolation; locked dependency Git metadata is packaged so Lake can validate revisions without cloning.
- `R`: two independent Ubuntu builders canonicalize volatile dependency Git metadata and must produce byte-identical archive, workspace-tree, and part-set fingerprints.

The server derives these values from a workflow-produced JSON evidence record. Schema `3.1.0` binds new evidence to an allow-listed `profileId`; legacy schema `3.0.0` remains valid only for the original `lean-4.32.2` profile. Before `FINAL VERIFIED` is possible, the server also runs `gh attestation verify` against the raw evidence bytes and requires the canonical repository, build workflow, source commit, configured source ref, and a GitHub-hosted runner. `POST /api/certification/evaluate` rejects client predicate assignment, and the old simulated reconstruction, self-test, and gate-evidence routes no longer return synthetic success.

No code path may emit `FINAL VERIFIED` unless both of these commands have returned exit code `0` in the primary build and in both offline reconstructions:

```bash
lake build
lake env lean MathlibSmoke.lean
```

`MathlibSmoke.lean` imports `Mathlib` and exercises `simp`, `norm_num`, `ring`, `aesop`, and `omega`. `InvalidTheorem.lean` is required to fail.

## Optional two-layer project certificate

Projects that combine exact Lean proofs with numerical geometry, trigonometry,
floating-point, or external scientific computation can add a separate project
certificate. This does not change or weaken `C_final` for the toolchain. It adds
an explicitly scoped result:

```text
C_project = A AND C_toolchain AND K_Lean AND W_external AND N_Lean AND N_external
```

- `A`: the exact project-evidence bytes have a GitHub attestation from the configured project repository, workflow, commit, source ref, and a GitHub-hosted runner.
- `C_toolchain`: the project names an allow-listed profile and the SHA-256 of the independently FINAL VERIFIED toolchain evidence loaded by the server.
- `K_Lean`: Lean successfully checks the exact finite aggregation theorem and its axiom-audit command; the source, executable, and logs are content-addressed.
- `W_external`: an independent verifier successfully checks every entry in the frozen component bank under a content-addressed numerical policy. Its executable, input, count, and log are recorded.
- `N_Lean`: a deliberately malformed aggregation is rejected.
- `N_external`: a deliberately mutated numerical witness is rejected.

This split is useful when the theorem depends on precomputed numerical facts:
Lean proves how accepted local facts aggregate, while the independent verifier
checks how those local facts were calculated. The certificate never relabels
SciPy, floating-point, or trigonometric evaluation as a Lean proof.

The portable contract is [project-certificate.schema.json](project-certificate.schema.json).
It accepts any positive component count (including an 808-component bank); the
count is not hard-coded. A project workflow should freeze and hash its component
bank and numerical-policy file, run both positive layers and both negative
controls, then write the actual commands, exit codes, executable/input/log
hashes, project revision, and base-toolchain evidence hash into one JSON record.

Run the structural/semantic preflight with:

```bash
npm run certify:project -- \
  project-certification-evidence.json \
  verified-toolchain-context.json \
  project-certification-verdict.json
```

The context file supplies `finalVerified`, `canonicalProfileId`, the raw base
evidence SHA-256, and an attestation result from the project workflow's own
acquisition step. That CLI output is deliberately limited to
`semanticVerified`; it cannot set `A` or emit project FINAL VERIFIED. The project
workflow should attest the finalized project-evidence file with GitHub artifact
attestations. The server then repeats the base evaluation, independently verifies
both attestations, and compares the evidence hashes before deriving `C_project`.

## Run the factory

Open **Actions → Build reproducible portable Lean toolchain → Run workflow** and choose `lean-4.32.2` or `lean-4.33.0-rc1`. Pushes to `main` continue to certify the stable default `lean-4.32.2` profile; the rc1 profile is dispatched explicitly so the two evidence streams cannot be confused.

The successful run uses two independent builders, evaluates their fingerprints, and then uploads connector-sized GitHub Actions artifacts:

- `portable-lean-toolchain-transport-index`: part checksums, the manifest, and acquisition/reconstruction helpers.
- `portable-lean-toolchain-part-NNN`: one payload part per artifact, discovered and uploaded dynamically from `part-sha256sums.txt` rather than a fixed slot list.
- `portable-lean-toolchain-verification`: the content-addressed certificate, manifest checksums, tree inventories, summary, and complete command logs.
- `portable-lean-toolchain-consumer-receipt`: proof that a downstream job downloaded the actual wrappers, verified and reconstructed them, then ran `lake build` and the smoke test using `--network none`.

GitHub wraps each artifact in a download ZIP. A single Actions artifact containing all parts would be about 2.45 GB and exceeds the 512 MiB binary-download limit of some connectors. Fan-out keeps every wrapper independently downloadable: each uncompressed payload part is less than 450 MiB, and `compression-level: 0` avoids expensive recompression.

From a checkout with an authenticated GitHub CLI, acquire a successful run by ID and verify all downloaded parts:

```bash
bash scripts/download-actions-artifacts.sh RUN_ID ./toolchain-download
```

In a connector-only environment, download `portable-lean-toolchain-transport-index`, each `portable-lean-toolchain-part-NNN` named by `part-sha256sums.txt`, and `portable-lean-toolchain-verification` individually. Extract the index and every part into one directory (put verification logs in a subdirectory if desired). The index is deliberately staged flat so the checksums, helpers, and downloaded parts share the layout expected below. This route uses Actions artifacts rather than release assets because some connectors expose release-asset metadata but no release-asset binary download operation.

After acquiring the individual artifacts, reconstruct with:

```bash
chmod +x verify-and-reconstruct.sh
./verify-and-reconstruct.sh . ./reconstructed
export PATH="$PWD/reconstructed/portable-lean-toolchain/lean/bin:$PATH"
cd reconstructed/portable-lean-toolchain/mathlib
lake build
lake env lean MathlibSmoke.lean
```

The acquisition helper refuses a non-successful workflow run and verifies the part hashes after download. The reconstruction helper requires `jq`, `sha256sum`, `tar`, and `unzstd`; it refuses missing, extra, duplicated, non-contiguous, checksum-mismatched, manifest-mismatched, or oversized parts, verifies the complete archive hash and byte count, and only then extracts into a new destination. If Actions retention has expired, run **Actions → Rehydrate certified release for connectors**. That workflow requires the release asset set to match its checksum inventory exactly, binds the release tag to the manifest/evidence/consumer commit, verifies all three original build-workflow attestations, re-evaluates the finalized evidence, and only then recreates and attests connector-sized artifacts. It does not rebuild or silently recertify the payload.

## Evidence API

Download `certification-evidence.json` from a successful workflow run and start the server with `CERTIFICATION_EVIDENCE_PATH` pointing to that file. The GitHub CLI must be installed and able to query attestations for `kolberz/Toolchain_factory`. `CERTIFICATION_SOURCE_REF` defaults to `refs/heads/main`; set it explicitly when viewing evidence legitimately produced on another ref. Optionally set `GITHUB_CLI_PATH` to the trusted `gh` executable and `TOOLCHAIN_MANIFEST_PATH` to the downloaded `toolchain-manifest.json`.

```bash
npm ci
CERTIFICATION_EVIDENCE_PATH=/absolute/path/certification-evidence.json \
CERTIFICATION_SOURCE_REF=refs/heads/main \
npm run dev
```

To evaluate an optional project certificate, also configure its evidence path
and exact attestation policy. Repository and workflow have no permissive
defaults because the factory cannot safely guess which external project is
trusted:

```bash
PROJECT_CERTIFICATION_EVIDENCE_PATH=/absolute/path/project-certification-evidence.json \
PROJECT_CERTIFICATION_REPOSITORY=owner/project \
PROJECT_CERTIFICATION_WORKFLOW=owner/project/.github/workflows/certify.yml \
PROJECT_CERTIFICATION_SOURCE_REF=refs/heads/main \
npm run dev
```

Useful endpoints:

- `GET /api/certification/status` — server-derived predicate evaluation.
- `GET /api/certification/evidence` — raw workflow evidence and evaluation.
- `GET /api/certification/gates` — immutable gate definitions, without canned results.
- `GET /api/project-certification/status` — optional two-layer project verdict.
- `GET /api/project-certification/evidence` — raw project evidence, attestation result, and derived predicates.
- `GET /api/manifest/anchors` — canonical upstream anchors.
- `GET /api/toolchain/bootstrap` — workflow and artifact contract.

Without workflow evidence, the honest status is `PENDING`. Evidence with invalid or unavailable attestation verification is `REJECTED`; upstream constants or structurally plausible JSON alone are not a portable-toolchain certificate.

## Local application checks

Every pull request runs these same lightweight application checks on
`ubuntu-24.04`; it does not launch the multi-gigabyte toolchain build.

```bash
npm ci
npm run lint
npm test
npm run build
```

The tests include independent evidence mutations covering corrupt part hashes, oversized parts, substituted executables, falsified expected-failure outcomes, stale reconstruction IDs, mismatched reconstruction trees, cross-builder disagreement, and failed authenticity verification. Project-certificate tests additionally attack the bound toolchain hash, component count, component-bank input, numerical-policy hash, Lean execution, and both negative controls. Each mutation must prevent final certification. The real build additionally injects an unlisted transport part and requires the public reconstruction helper to reject it.

## Trust boundary

GitHub Actions is the privileged build-and-download bridge. The certificate records the repository commit, workflow run, upstream anchors, executable digests, part digests and sizes, command definitions and exit codes, log digests, tree digest, independent reconstruction IDs, and two independent builder fingerprints. The workflow evaluates the actual finalized evidence, downloads its own uploaded artifacts as a consumer, and creates Sigstore-backed GitHub artifact attestations for the manifest, certificate, and consumer receipt. GitHub retains the uploaded content-addressed artifacts; the application keeps no mutable in-memory certification state.

Consumers must obtain artifacts from the expected GitHub repository/run, verify the provided SHA-256 files, and verify provenance with `gh attestation verify FILE -R kolberz/Toolchain_factory`. Attestations bind artifacts to the workflow identity and commit; they do not replace review of the build instructions or theorem trust model.
