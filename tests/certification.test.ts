import assert from 'node:assert/strict';
import test from 'node:test';
import {
  CANONICAL_ANCHORS,
  CANONICAL_PROFILES,
  DEFAULT_PROFILE_ID,
  GATE_DEFINITIONS,
  evaluateCertificationEvidence
} from '../certification.ts';

const sha = (character: string) => character.repeat(64);

function validEvidence(profileId = DEFAULT_PROFILE_ID): any {
  return {
    schemaVersion: '3.1.0',
    generatedAt: '2026-08-08T00:00:00Z',
    source: { repository: 'kolberz/Toolchain_factory', commit: 'a'.repeat(40), runId: '12345', runnerImage: 'ubuntu-24.04', builderInstance: '1' },
    anchors: { ...CANONICAL_PROFILES[profileId] },
    transport: {
      archiveSha256: sha('a'),
      workspaceTreeSha256: sha('b'),
      partSetSha256: sha('8'),
      verificationExitCode: 0,
      parts: [
        { filename: 'portable.tar.zst.part-000', sha256: sha('c'), bytes: 440 * 1024 * 1024 },
        { filename: 'portable.tar.zst.part-001', sha256: sha('d'), bytes: 1024 }
      ]
    },
    execution: {
      leanExecutableSha256: sha('e'),
      lakeExecutableSha256: sha('f'),
      gates: GATE_DEFINITIONS.map(gate => ({
        ...gate,
        actualExitCode: gate.expectedOutcome === 'PASS' ? 0 : 1,
        logSha256: sha('1')
      }))
    },
    offlineReconstructions: [0, 1].map(index => ({
      id: `offline-${index + 1}`,
      networkMode: 'none',
      lakeBuildExitCode: 0,
      smokeExitCode: 0,
      treeSha256: sha('b'),
      logSha256: sha(String(index + 2))
    })),
    reproducibility: {
      comparisonExitCode: 0,
      independentBuilders: 2,
      builders: ['builder-1', 'builder-2'].map(id => ({
        id,
        fingerprintSha256: sha('7'),
        archiveSha256: sha('a'),
        workspaceTreeSha256: sha('b'),
        partSetSha256: sha('8')
      }))
    }
  };
}

test('derives FINAL VERIFIED only from complete workflow evidence', () => {
  const result = evaluateCertificationEvidence(validEvidence());
  assert.equal(result.finalVerified, true);
  assert.deepEqual(Object.values(result.predicates).map(value => value.value), [true, true, true, true, true, true]);
});

test('derives FINAL VERIFIED for the exact Lean 4.33.0-rc1 profile', () => {
  const result = evaluateCertificationEvidence(validEvidence('lean-4.33.0-rc1'));
  assert.equal(result.finalVerified, true);
  assert.equal(result.canonicalProfileId, 'lean-4.33.0-rc1');
  assert.equal(result.canonicalAnchors.leanToolchain, 'leanprover/lean4:v4.33.0-rc1');
});

test('derives FINAL VERIFIED for the exact Lean 4.33.0-rc2 profile', () => {
  const result = evaluateCertificationEvidence(validEvidence('lean-4.33.0-rc2'));
  assert.equal(result.finalVerified, true);
  assert.equal(result.canonicalProfileId, 'lean-4.33.0-rc2');
  assert.equal(result.canonicalAnchors.leanToolchain, 'leanprover/lean4:v4.33.0-rc2');
  assert.equal(result.canonicalAnchors.mathlibCommit, '51e6992efd06126df61a496bebf8f49482a4e129');
});

test('continues to verify legacy schema 3.0.0 evidence against the 4.32.2 profile', () => {
  const evidence = validEvidence();
  evidence.schemaVersion = '3.0.0';
  delete evidence.anchors.profileId;
  delete evidence.anchors.leanVersion;
  const result = evaluateCertificationEvidence(evidence);
  assert.equal(result.finalVerified, true);
  assert.equal(result.canonicalProfileId, DEFAULT_PROFILE_ID);
});

test('rejects mixed-version profile anchors', () => {
  const evidence = validEvidence('lean-4.33.0-rc1');
  evidence.anchors.mathlibCommit = CANONICAL_ANCHORS.mathlibCommit;
  assert.equal(evaluateCertificationEvidence(evidence).finalVerified, false);
});

test('rejects rc2 evidence carrying an rc1 Mathlib anchor', () => {
  const evidence = validEvidence('lean-4.33.0-rc2');
  evidence.anchors.mathlibCommit = CANONICAL_PROFILES['lean-4.33.0-rc1'].mathlibCommit;
  assert.equal(evaluateCertificationEvidence(evidence).finalVerified, false);
});

test('rejects a non-allow-listed profile', () => {
  const evidence = validEvidence('lean-4.33.0-rc1');
  evidence.anchors.profileId = 'lean-4.33-compatible-ish';
  assert.equal(evaluateCertificationEvidence(evidence).finalVerified, false);
});

test('rejects semantically valid evidence when authenticity verification fails', () => {
  const result = evaluateCertificationEvidence(validEvidence(), 'synthetic evidence', {
    provenanceReasons: ['Evidence authenticity was not verified: no matching GitHub attestation.']
  });
  assert.equal(result.finalVerified, false);
  assert.equal(result.predicates.P.value, false);
  assert.match(result.predicates.P.reasons.join(' '), /authenticity was not verified/i);
});

test('does not accept predicate booleans as evidence', () => {
  const result = evaluateCertificationEvidence({ P: true, T: true, E: true, O_1: true, O_2: true, R: true });
  assert.equal(result.finalVerified, false);
});

for (const attack of [
  ['mutated part hash', (e: any) => { e.transport.parts[0].sha256 = 'not-a-hash'; }],
  ['oversized part', (e: any) => { e.transport.parts[0].bytes = 450 * 1024 * 1024; }],
  ['substituted executable', (e: any) => { e.execution.leanExecutableSha256 = 'substituted'; }],
  ['falsified negative exit code', (e: any) => { e.execution.gates.find((g: any) => g.id === 'invalid-theorem').actualExitCode = 0; }],
  ['stale reconstruction ID', (e: any) => { e.offlineReconstructions[1].id = 'offline-1'; }],
  ['mismatched reconstruction tree', (e: any) => { e.offlineReconstructions[0].treeSha256 = sha('9'); }],
  ['cross-builder archive mismatch', (e: any) => { e.reproducibility.builders[1].archiveSha256 = sha('9'); }]
] as const) {
  test(`rejects actual evidence mutation: ${attack[0]}`, () => {
    const evidence = validEvidence();
    attack[1](evidence);
    assert.equal(evaluateCertificationEvidence(evidence).finalVerified, false);
  });
}
