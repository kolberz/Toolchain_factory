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
| `lean-4.33.0-rc2` | `v4.33.0-rc2` | `51e6992efd06126df61a496bebf8f49482a4e129` | `48010c7d6264dc992574e9b0e09ece1f9c648e8f5106066b2cdb6834a6a60a6c` |

The rc profiles exist for projects already pinned to their exact prerelease.
They are separate toolchains, not a claim that 4.33 compiled artifacts are
backward-compatible with 4.32, or that rc1 and rc2 oleans are interchangeable.
The certified 4.32.2 release remains immutable.

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

## Run the factory

Open **Actions → Build reproducible portable Lean toolchain → Run workflow**
and choose `lean-4.32.2`, `lean-4.33.0-rc1`, or `lean-4.33.0-rc2`.
Pushes to `main` continue to certify the stable default `lean-4.32.2`
profile; prerelease profiles are dispatched explicitly so their evidence
streams cannot be confused.

For the exact Anthropic Zeta23 consumer described below, choose
`lean-4.33.0-rc2` and enable **Run the exact Anthropic Zeta23 consumer
certificate**. The workflow rejects that option with any other profile.

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

## Exact Anthropic Zeta23 consumer certificate

`zeta23-profile.json` defines a separate, fail-closed consumer profile for
[`anthropics/zeta-23-lean`](https://github.com/anthropics/zeta-23-lean) at
commit `3635e74826a4c1fcece7d1cd2b6fa75e43a00510`. It requires the exact
`lean-4.33.0-rc2` factory profile and Mathlib commit
`51e6992efd06126df61a496bebf8f49482a4e129`; there is no 4.32-to-4.33
compatibility shim.

The consumer has two deliberately distinct verdicts:

```text
Z_core   = T AND S AND B AND A
Z_strong = Z_core AND C_base AND C_multiplicity AND C_xiprime
```

- `T` authenticates and re-evaluates the factory certificate, verifies the
  exact rc2 profile, reconstructs its hashed parts, records the actual Lean and
  Lake binary hashes, and runs the Zeta core in Docker with `--network none`.
- `S` requires the exact Zeta source commit and exact hashes/sizes for its
  `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`. A changed tracked
  source file rejects the certificate.
- `B` requires exit code zero from `lake build` and
  `lake build Solution Solution.Multiplicity Solution.XiPrime`, with no `sorry`
  warning from `Zeta23/` or the Solution modules.
- `A` parses the actual four `#print axioms` logs. Each of the 15 base, 12
  multiplicity, and 6 XiPrime headline declarations must report exactly
  `[propext, Classical.choice, Quot.sound]`.
- Each `C_*` result starts from a fresh checkout with no existing Solution
  olean, validates its source-owned comparator configuration, and requires the
  pinned real `landrun`, matching `lean4export`, the Lean kernel replay, and the
  independent `nanoda` kernel. A write-denial probe and the documented
  unprivileged `systemd-run` boundary must pass. There is no fake-landrun
  fallback.

The bandwidth-one PairCeiling audit is reported separately. Its nine analytic
declarations must use the standard three axioms, `LawN256_check` must use only
`propext`, and `LawN256_edge` must be axiom-free. The result remains explicitly
conditional on the displayed external `EnclOK` hypothesis; it is never folded
into the unconditional Zeta headline.

The successful job uploads and attests `zeta23-evidence.json`, its independently
recomputed verdict, all command logs, source-tree inventory, tool hashes, and
SHA-256 files as `zeta23-verification-evidence`. A build success by itself is
not a strong certificate: only `strongVerified: true` after all three fresh
comparator/nanoda runs is the strong result.

All remote GitHub Actions used by the build, rehydration, and Zeta workflows are
pinned to immutable commit SHAs. The offline Ubuntu verifier image is likewise
pinned by registry digest; tool source commits, clean tracked working trees,
executed binary hashes, reconstruction output, and sandbox logs remain
part of the reviewable evidence boundary.

## Evidence API

Download `certification-evidence.json` from a successful workflow run and start the server with `CERTIFICATION_EVIDENCE_PATH` pointing to that file. The GitHub CLI must be installed and able to query attestations for `kolberz/Toolchain_factory`. `CERTIFICATION_SOURCE_REF` defaults to `refs/heads/main`; set it explicitly when viewing evidence legitimately produced on another ref. Optionally set `GITHUB_CLI_PATH` to the trusted `gh` executable and `TOOLCHAIN_MANIFEST_PATH` to the downloaded `toolchain-manifest.json`.

```bash
npm ci
CERTIFICATION_EVIDENCE_PATH=/absolute/path/certification-evidence.json \
CERTIFICATION_SOURCE_REF=refs/heads/main \
npm run dev
```

Useful endpoints:

- `GET /api/certification/status` — server-derived predicate evaluation.
- `GET /api/certification/evidence` — raw workflow evidence and evaluation.
- `GET /api/certification/gates` — immutable gate definitions, without canned results.
- `GET /api/manifest/anchors` — canonical upstream anchors.
- `GET /api/toolchain/bootstrap` — workflow and artifact contract.

Without workflow evidence, the honest status is `PENDING`. Evidence with invalid or unavailable attestation verification is `REJECTED`; upstream constants or structurally plausible JSON alone are not a portable-toolchain certificate.

## Local application checks

```bash
npm ci
npm run lint
npm test
npm run build
```

The tests include independent evidence mutations covering corrupt part hashes, oversized parts, substituted executables, falsified expected-failure outcomes, stale reconstruction IDs, mismatched reconstruction trees, cross-builder disagreement, and failed authenticity verification. Each mutation must prevent final certification. The real build additionally injects an unlisted transport part and requires the public reconstruction helper to reject it.

## Trust boundary

GitHub Actions is the privileged build-and-download bridge. The certificate records the repository commit, workflow run, upstream anchors, executable digests, part digests and sizes, command definitions and exit codes, log digests, tree digest, independent reconstruction IDs, and two independent builder fingerprints. The workflow evaluates the actual finalized evidence, downloads its own uploaded artifacts as a consumer, and creates Sigstore-backed GitHub artifact attestations for the manifest, certificate, and consumer receipt. GitHub retains the uploaded content-addressed artifacts; the application keeps no mutable in-memory certification state.

Consumers must obtain artifacts from the expected GitHub repository/run, verify the provided SHA-256 files, and verify provenance with `gh attestation verify FILE -R kolberz/Toolchain_factory`. Attestations bind artifacts to the workflow identity and commit; they do not replace review of the build instructions or theorem trust model.
