import assert from 'node:assert/strict';
import test from 'node:test';
import { evaluateProjectCertificationEvidence, type VerifiedToolchainContext } from '../project-certification.ts';

const sha = (character: string) => character.repeat(64);

const toolchain: VerifiedToolchainContext = {
  finalVerified: true,
  attestationVerified: true,
  canonicalProfileId: 'lean-4.33.0-rc1',
  evidenceSha256: sha('a')
};

function validEvidence(): any {
  return {
    schemaVersion: '1.0.0',
    generatedAt: '2026-08-11T00:00:00Z',
    source: {
      repository: 'kolberz/example-project',
      commit: 'b'.repeat(40),
      runId: '45678',
      workflow: 'kolberz/example-project/.github/workflows/certify.yml',
      runnerImage: 'ubuntu-24.04'
    },
    project: {
      id: 'frozen-component-bank',
      revision: 'v45',
      componentBankSha256: sha('c'),
      componentCount: 808
    },
    toolchain: {
      profileId: 'lean-4.33.0-rc1',
      certificationEvidenceSha256: sha('a')
    },
    leanAggregation: {
      command: 'lake env lean CertifiedAggregation.lean',
      theorem: 'component_bound',
      sourceSha256: sha('d'),
      leanExecutableSha256: sha('e'),
      exitCode: 0,
      logSha256: sha('f'),
      axiomsCommand: 'lake env lean AxiomAudit.lean',
      axiomsExitCode: 0,
      axiomsLogSha256: sha('1')
    },
    externalVerification: {
      verifierName: 'component-witness-verifier',
      verifierVersion: '1.0.0',
      verifierExecutableSha256: sha('2'),
      command: './verify-components component-bank.json numeric-policy.json',
      inputSha256: sha('c'),
      numericPolicySha256: sha('3'),
      verifiedComponentCount: 808,
      exitCode: 0,
      logSha256: sha('4')
    },
    negativeControls: {
      lean: {
        id: 'malformed-aggregation',
        command: 'lake env lean InvalidAggregation.lean',
        mutatedInputSha256: sha('5'),
        exitCode: 1,
        logSha256: sha('6')
      },
      external: {
        id: 'mutated-witness',
        command: './verify-components mutated-component-bank.json numeric-policy.json',
        mutatedInputSha256: sha('7'),
        exitCode: 2,
        logSha256: sha('8')
      }
    }
  };
}

const authenticated = { authenticated: true, rawEvidenceSha256: sha('9') };

test('derives project FINAL VERIFIED from authenticated two-layer evidence', () => {
  const result = evaluateProjectCertificationEvidence(validEvidence(), toolchain, 'test evidence', authenticated);
  assert.equal(result.semanticVerified, true);
  assert.equal(result.finalVerified, true);
  assert.equal(result.componentCount, 808);
  assert.deepEqual(Object.values(result.predicates).map(value => value.value), [true, true, true, true, true, true]);
});

test('keeps valid pre-attestation evidence at semantic verification only', () => {
  const result = evaluateProjectCertificationEvidence(validEvidence(), toolchain);
  assert.equal(result.semanticVerified, true);
  assert.equal(result.finalVerified, false);
  assert.equal(result.predicates.A.value, false);
  assert.match(result.status, /ATTESTATION REQUIRED/);
});

test('rejects a project bound to a different certified toolchain evidence hash', () => {
  const evidence = validEvidence();
  evidence.toolchain.certificationEvidenceSha256 = sha('0');
  const result = evaluateProjectCertificationEvidence(evidence, toolchain, 'test evidence', authenticated);
  assert.equal(result.finalVerified, false);
  assert.equal(result.predicates.C_toolchain.value, false);
});

test('rejects a toolchain verdict that was not authenticated', () => {
  const result = evaluateProjectCertificationEvidence(
    validEvidence(),
    { ...toolchain, attestationVerified: false },
    'test evidence',
    authenticated
  );
  assert.equal(result.finalVerified, false);
  assert.equal(result.predicates.C_toolchain.value, false);
});

for (const attack of [
  ['unaccounted component', (e: any) => { e.externalVerification.verifiedComponentCount = 807; }, 'W_external'],
  ['substituted numerical policy', (e: any) => { e.externalVerification.numericPolicySha256 = 'not-a-hash'; }, 'W_external'],
  ['component-bank substitution', (e: any) => { e.externalVerification.inputSha256 = sha('0'); }, 'W_external'],
  ['Lean compilation failure', (e: any) => { e.leanAggregation.exitCode = 1; }, 'K_Lean'],
  ['Lean negative control unexpectedly succeeds', (e: any) => { e.negativeControls.lean.exitCode = 0; }, 'N_Lean'],
  ['external negative control unexpectedly succeeds', (e: any) => { e.negativeControls.external.exitCode = 0; }, 'N_external'],
  ['unchanged external negative input', (e: any) => { e.negativeControls.external.mutatedInputSha256 = e.project.componentBankSha256; }, 'N_external']
] as const) {
  test(`rejects project evidence mutation: ${attack[0]}`, () => {
    const evidence = validEvidence();
    attack[1](evidence);
    const result = evaluateProjectCertificationEvidence(evidence, toolchain, 'test evidence', authenticated);
    assert.equal(result.finalVerified, false);
    assert.equal(result.predicates[attack[2]].value, false);
  });
}

test('does not accept project predicate booleans as evidence', () => {
  const result = evaluateProjectCertificationEvidence(
    { A: true, C_toolchain: true, K_Lean: true, W_external: true, N_Lean: true, N_external: true },
    toolchain,
    'client body',
    authenticated
  );
  assert.equal(result.finalVerified, false);
});
