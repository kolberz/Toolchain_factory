import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { evaluateProjectCertificationEvidence, type VerifiedToolchainContext } from '../project-certification.ts';

const [projectEvidencePath, toolchainVerdictPath, verdictPath] = process.argv.slice(2);
if (!projectEvidencePath || !toolchainVerdictPath || !verdictPath) {
  console.error('usage: tsx scripts/evaluate-project-evidence.ts PROJECT_EVIDENCE_JSON TOOLCHAIN_VERDICT_JSON PROJECT_VERDICT_JSON');
  process.exit(64);
}

const rawProjectEvidence = readFileSync(projectEvidencePath);
const projectEvidence = JSON.parse(rawProjectEvidence.toString('utf8'));
const toolchainVerdict = JSON.parse(readFileSync(toolchainVerdictPath, 'utf8'));
const toolchain: VerifiedToolchainContext = {
  finalVerified: toolchainVerdict?.finalVerified === true,
  attestationVerified: toolchainVerdict?.attestation?.verified === true,
  canonicalProfileId: typeof toolchainVerdict?.canonicalProfileId === 'string' ? toolchainVerdict.canonicalProfileId : null,
  evidenceSha256: typeof toolchainVerdict?.rawEvidenceSha256 === 'string'
    ? toolchainVerdict.rawEvidenceSha256
    : typeof toolchainVerdict?.evidenceSha256 === 'string' ? toolchainVerdict.evidenceSha256 : null
};
const rawEvidenceSha256 = createHash('sha256').update(rawProjectEvidence).digest('hex');
const evaluation = evaluateProjectCertificationEvidence(
  projectEvidence,
  toolchain,
  projectEvidencePath,
  {
    authenticated: false,
    authenticationReasons: ['Semantic evaluation completed before project evidence attestation verification.'],
    rawEvidenceSha256
  }
);
const verdict = {
  schemaVersion: '1.0.0',
  rawEvidenceSha256,
  note: 'semanticVerified is the workflow pre-attestation gate; FINAL VERIFIED additionally requires server-side attestation verification.',
  ...evaluation
};
writeFileSync(verdictPath, `${JSON.stringify(verdict, null, 2)}\n`);
console.log(JSON.stringify(verdict, null, 2));
if (!evaluation.semanticVerified) process.exit(1);
