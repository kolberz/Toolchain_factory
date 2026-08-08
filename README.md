# Toolchain Factory

Toolchain Factory builds a genuine, portable Linux x86-64 Lean 4 + Lake + Mathlib environment on a GitHub-hosted Ubuntu runner. The browser application is an evidence viewer; it does not pretend to download artifacts, run Lean, or assign certification predicates.

## Pinned upstream

- Lean toolchain: `leanprover/lean4:v4.32.2`
- Mathlib tag: `v4.32.2`
- Mathlib commit: `905b95818eb32af7874a58b427f50c1711a5e96c`
- Mathlib release dependency-lock SHA-256: `015c7e00ead0f05f2a72b32d9bdef782d4689d05a6297f0ceb0ab5d196c164bd`
- Official Lean release: `lean-4.32.2-linux.tar.zst`
- Release SHA-256: `5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa`
- Release size: `563991635` bytes

The workflow downloads the official release, verifies both its full 64-character SHA-256 and exact size, clones the exact Mathlib tag, verifies the resolved commit and `lean-toolchain`, runs `lake update`, and obtains Mathlib's compiled cache with `lake exe cache get`. Because dependency default branches can move after a release, the workflow restores and verifies the release's content-addressed `lake-manifest.json` after the required `lake update`, then fetches/builds that locked dependency graph.

## Certification model

The final predicate is:

```text
C_final = P AND T AND E AND O_1 AND O_2
```

- `P`: the release, toolchain, Mathlib tag, and Mathlib commit match the canonical anchors above.
- `T`: every generated archive part has a valid SHA-256, checksum verification exits zero, the reassembled archive hash matches, and every part is strictly smaller than 450 MiB.
- `E`: the workflow executes the server-owned gates with their expected outcomes. Positive gates must exit zero; the deliberately invalid theorem must exit nonzero.
- `O_1` and `O_2`: two separate extraction roots reproduce the packaged tree hash and run `lake build` plus `lake env lean MathlibSmoke.lean` in separate Docker containers using `--network none`. The verifier image and its Git executable are prepared before isolation; locked dependency Git metadata is packaged so Lake can validate revisions without cloning.

The server derives these values from a workflow-produced JSON evidence record. `POST /api/certification/evaluate` rejects client predicate assignment, and the old simulated reconstruction, self-test, and gate-evidence routes no longer return synthetic success.

No code path may emit `FINAL VERIFIED` unless both of these commands have returned exit code `0` in the primary build and in both offline reconstructions:

```bash
lake build
lake env lean MathlibSmoke.lean
```

`MathlibSmoke.lean` imports `Mathlib` and exercises `simp`, `norm_num`, `ring`, `aesop`, and `omega`. `InvalidTheorem.lean` is required to fail.

## Run the factory

Open **Actions → Build portable Lean toolchain → Run workflow**. The workflow is also triggered when its build inputs land on `main`.

The successful run uploads two GitHub Actions artifacts:

- `portable-lean-toolchain-parts`: every split archive part, part checksums, the manifest, and the reconstruction helper.
- `portable-lean-toolchain-verification`: the content-addressed certificate, manifest checksums, tree inventories, summary, and complete command logs.

GitHub wraps each artifact in a download ZIP. The actual portable payload inside the first artifact is a multipart `tar.zst`; each payload part is less than 450 MiB.

After downloading and unzipping `portable-lean-toolchain-parts`, reconstruct with:

```bash
chmod +x verify-and-reconstruct.sh
./verify-and-reconstruct.sh . ./reconstructed
export PATH="$PWD/reconstructed/portable-lean-toolchain/lean/bin:$PATH"
cd reconstructed/portable-lean-toolchain/mathlib
lake build
lake env lean MathlibSmoke.lean
```

The helper refuses missing parts, checksum mismatches, oversized parts, and a pre-existing destination.

## Evidence API

Download `certification-evidence.json` from a successful workflow run and start the server with `CERTIFICATION_EVIDENCE_PATH` pointing to that file. Optionally set `TOOLCHAIN_MANIFEST_PATH` to the downloaded `toolchain-manifest.json`.

```bash
npm ci
CERTIFICATION_EVIDENCE_PATH=/absolute/path/certification-evidence.json npm run dev
```

Useful endpoints:

- `GET /api/certification/status` — server-derived predicate evaluation.
- `GET /api/certification/evidence` — raw workflow evidence and evaluation.
- `GET /api/certification/gates` — immutable gate definitions, without canned results.
- `GET /api/manifest/anchors` — canonical upstream anchors.
- `GET /api/toolchain/bootstrap` — workflow and artifact contract.

Without workflow evidence, the honest status is `PENDING`; upstream constants alone are not a portable-toolchain certificate.

## Local application checks

```bash
npm ci
npm run lint
npm test
npm run build
```

The tests include six independent evidence mutations: corrupt part hash, oversized part, substituted executable digest, falsified expected-failure outcome, stale reconstruction ID, and mismatched reconstruction tree. Each mutation must prevent final certification.

## Trust boundary

GitHub Actions is the privileged build-and-download bridge. The certificate records the repository commit, workflow run, upstream anchors, executable digests, part digests and sizes, command definitions and exit codes, log digests, tree digest, and independent reconstruction IDs. GitHub retains the uploaded content-addressed artifacts; the application keeps no mutable in-memory certification state.

This is evidence-based certification, not a signature scheme. Consumers must obtain artifacts from the expected GitHub repository/run, verify the provided SHA-256 files, and apply their own GitHub identity and retention policy requirements.
