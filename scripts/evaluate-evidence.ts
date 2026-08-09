import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';
import { evaluateCertificationEvidence } from '../certification.ts';

const [evidencePath, verdictPath] = process.argv.slice(2);
if (!evidencePath || !verdictPath) {
  console.error('usage: tsx scripts/evaluate-evidence.ts EVIDENCE_JSON VERDICT_JSON');
  process.exit(64);
}

const rawEvidence = readFileSync(evidencePath);
const evidence = JSON.parse(rawEvidence.toString('utf8'));
const evaluation = evaluateCertificationEvidence(evidence, evidencePath);
const verdict = {
  schemaVersion: '1.0.0',
  rawEvidenceSha256: createHash('sha256').update(rawEvidence).digest('hex'),
  ...evaluation
};
writeFileSync(verdictPath, `${JSON.stringify(verdict, null, 2)}\n`);
console.log(JSON.stringify(verdict, null, 2));
if (!evaluation.finalVerified) process.exit(1);
