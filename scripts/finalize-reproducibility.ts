import { createHash } from 'node:crypto';
import { readFileSync, writeFileSync } from 'node:fs';

const [evidencePath, firstPath, secondPath] = process.argv.slice(2);
if (!evidencePath || !firstPath || !secondPath) {
  console.error('usage: tsx scripts/finalize-reproducibility.ts EVIDENCE_JSON BUILDER_1_JSON BUILDER_2_JSON');
  process.exit(64);
}

const firstRaw = readFileSync(firstPath);
const secondRaw = readFileSync(secondPath);
const first = JSON.parse(firstRaw.toString('utf8'));
const second = JSON.parse(secondRaw.toString('utf8'));
const equal = firstRaw.equals(secondRaw);
const evidence = JSON.parse(readFileSync(evidencePath, 'utf8'));

const summarize = (id: string, fingerprint: any, raw: Buffer) => ({
  id,
  fingerprintSha256: createHash('sha256').update(raw).digest('hex'),
  archiveSha256: fingerprint.transport?.archiveSha256,
  workspaceTreeSha256: fingerprint.transport?.workspaceTreeSha256,
  partSetSha256: fingerprint.transport?.partSetSha256
});

evidence.reproducibility = {
  comparisonExitCode: equal ? 0 : 1,
  independentBuilders: 2,
  builders: [summarize('builder-1', first, firstRaw), summarize('builder-2', second, secondRaw)]
};
writeFileSync(evidencePath, `${JSON.stringify(evidence, null, 2)}\n`);

if (!equal) {
  console.error('Independent builder fingerprints differ.');
  console.error(JSON.stringify({ builder1: first, builder2: second }, null, 2));
  process.exit(1);
}
console.log(`independent builders match: ${evidence.reproducibility.builders[0].fingerprintSha256}`);
