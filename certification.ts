import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';

export const CANONICAL_ANCHORS = Object.freeze({
  leanToolchain: 'leanprover/lean4:v4.32.2',
  mathlibTag: 'v4.32.2',
  mathlibCommit: '905b95818eb32af7874a58b427f50c1711a5e96c',
  releaseArtifact: 'lean-4.32.2-linux.tar.zst',
  releaseTarballSha256: '5f2069e6f5db73780f374ccb49ce8ea649aa20a0cebf0116816744c999ce72aa',
  releaseTarballBytes: 563_991_635,
  architecture: 'linux-x86_64'
});

export const GATE_DEFINITIONS = Object.freeze([
  { id: 'lean-version', command: 'lean --version', expectedOutcome: 'PASS' },
  { id: 'lake-update', command: 'lake update', expectedOutcome: 'PASS' },
  { id: 'mathlib-cache', command: 'lake exe cache get', expectedOutcome: 'PASS' },
  { id: 'lake-build', command: 'lake build', expectedOutcome: 'PASS' },
  { id: 'mathlib-smoke', command: 'lake env lean MathlibSmoke.lean', expectedOutcome: 'PASS' },
  { id: 'invalid-theorem', command: 'lake env lean InvalidTheorem.lean', expectedOutcome: 'FAIL' }
]);

const SHA256 = /^[0-9a-f]{64}$/;
const MAX_PART_BYTES = 450 * 1024 * 1024;

export interface PredicateResult {
  name: string;
  value: boolean;
  state: 'VERIFIED' | 'FAILED' | 'PENDING';
  reasons: string[];
}

export interface CertificationEvaluation {
  status: string;
  formula: string;
  finalVerified: boolean;
  predicates: Record<'P' | 'T' | 'E' | 'O_1' | 'O_2', PredicateResult>;
  canonicalAnchors: typeof CANONICAL_ANCHORS;
  evidenceSha256: string | null;
  evidenceSource: string;
  generatedAt: string | null;
}

function get(record: unknown, keys: string[]): unknown {
  let current = record as any;
  for (const key of keys) current = current && typeof current === 'object' ? current[key] : undefined;
  return current;
}

function isSha256(value: unknown): value is string {
  return typeof value === 'string' && SHA256.test(value);
}

function predicate(name: string, reasons: string[], pending = false): PredicateResult {
  return {
    name,
    value: reasons.length === 0 && !pending,
    state: pending ? 'PENDING' : reasons.length === 0 ? 'VERIFIED' : 'FAILED',
    reasons
  };
}

export function evaluateCertificationEvidence(evidence: unknown, evidenceSource = 'server-owned evidence file'): CertificationEvaluation {
  if (!evidence || typeof evidence !== 'object') {
    const pending = (name: string) => predicate(name, ['No workflow evidence has been loaded.'], true);
    return {
      status: 'PENDING — GITHUB ACTIONS EVIDENCE NOT LOADED',
      formula: 'C_final = P AND T AND E AND O_1 AND O_2 = false',
      finalVerified: false,
      predicates: {
        P: pending('official provenance anchors verified'),
        T: pending('archive parts hash-verified and bounded below 450 MiB'),
        E: pending('real Lean, Lake, Mathlib, tactic, and negative gates executed'),
        O_1: pending('network-isolated reconstruction #1 executed'),
        O_2: pending('network-isolated reconstruction #2 executed')
      },
      canonicalAnchors: CANONICAL_ANCHORS,
      evidenceSha256: null,
      evidenceSource,
      generatedAt: null
    };
  }

  const provenanceReasons: string[] = [];
  const anchors = get(evidence, ['anchors']) as any;
  for (const [key, expected] of Object.entries(CANONICAL_ANCHORS)) {
    if (anchors?.[key] !== expected) provenanceReasons.push(`${key} does not match the canonical anchor.`);
  }

  const transportReasons: string[] = [];
  const parts = get(evidence, ['transport', 'parts']);
  if (!Array.isArray(parts) || parts.length === 0) {
    transportReasons.push('No transport parts were recorded.');
  } else {
    const names = new Set<string>();
    for (const part of parts) {
      if (!part || typeof part.filename !== 'string' || names.has(part.filename)) transportReasons.push('Part filenames must be present and unique.');
      else names.add(part.filename);
      if (!isSha256(part?.sha256)) transportReasons.push(`Part ${part?.filename || '<unknown>'} has an invalid SHA-256.`);
      if (!Number.isInteger(part?.bytes) || part.bytes <= 0 || part.bytes >= MAX_PART_BYTES) {
        transportReasons.push(`Part ${part?.filename || '<unknown>'} is not smaller than 450 MiB.`);
      }
    }
  }
  if (!isSha256(get(evidence, ['transport', 'archiveSha256']))) transportReasons.push('Archive SHA-256 is missing or invalid.');
  if (!isSha256(get(evidence, ['transport', 'workspaceTreeSha256']))) transportReasons.push('Workspace tree SHA-256 is missing or invalid.');
  if (get(evidence, ['transport', 'verificationExitCode']) !== 0) transportReasons.push('Transport checksum verification did not exit 0.');

  const executionReasons: string[] = [];
  const gates = get(evidence, ['execution', 'gates']);
  if (!Array.isArray(gates)) {
    executionReasons.push('Execution gate records are missing.');
  } else {
    for (const definition of GATE_DEFINITIONS) {
      const gate = gates.find((candidate: any) => candidate?.id === definition.id);
      if (!gate) {
        executionReasons.push(`Gate ${definition.id} is missing.`);
        continue;
      }
      if (gate.command !== definition.command || gate.expectedOutcome !== definition.expectedOutcome) {
        executionReasons.push(`Gate ${definition.id} does not match its server-owned definition.`);
      }
      const actualOutcome = gate.actualExitCode === 0 ? 'PASS' : 'FAIL';
      if (actualOutcome !== definition.expectedOutcome) executionReasons.push(`Gate ${definition.id} produced ${actualOutcome}, expected ${definition.expectedOutcome}.`);
      if (!isSha256(gate.logSha256)) executionReasons.push(`Gate ${definition.id} log SHA-256 is invalid.`);
    }
  }
  if (!isSha256(get(evidence, ['execution', 'leanExecutableSha256']))) executionReasons.push('Lean executable SHA-256 is invalid.');
  if (!isSha256(get(evidence, ['execution', 'lakeExecutableSha256']))) executionReasons.push('Lake executable SHA-256 is invalid.');

  const reconstructions = get(evidence, ['offlineReconstructions']);
  const offlineReasons = (index: number): string[] => {
    const reasons: string[] = [];
    const reconstruction = Array.isArray(reconstructions) ? reconstructions[index] : undefined;
    if (!reconstruction) return [`Offline reconstruction #${index + 1} is missing.`];
    if (reconstruction.id !== `offline-${index + 1}`) reasons.push(`Offline reconstruction #${index + 1} has the wrong independent ID.`);
    if (reconstruction.networkMode !== 'none') reasons.push(`Offline reconstruction #${index + 1} was not run with networkMode=none.`);
    if (reconstruction.lakeBuildExitCode !== 0) reasons.push(`Offline reconstruction #${index + 1} lake build did not exit 0.`);
    if (reconstruction.smokeExitCode !== 0) reasons.push(`Offline reconstruction #${index + 1} Mathlib smoke test did not exit 0.`);
    if (!isSha256(reconstruction.treeSha256)) reasons.push(`Offline reconstruction #${index + 1} tree SHA-256 is invalid.`);
    if (reconstruction.treeSha256 !== get(evidence, ['transport', 'workspaceTreeSha256'])) reasons.push(`Offline reconstruction #${index + 1} tree SHA-256 does not match the packaged workspace.`);
    if (!isSha256(reconstruction.logSha256)) reasons.push(`Offline reconstruction #${index + 1} log SHA-256 is invalid.`);
    return reasons;
  };

  const predicates = {
    P: predicate('official provenance anchors verified', provenanceReasons),
    T: predicate('archive parts hash-verified and bounded below 450 MiB', transportReasons),
    E: predicate('real Lean, Lake, Mathlib, tactic, and negative gates executed', executionReasons),
    O_1: predicate('network-isolated reconstruction #1 executed', offlineReasons(0)),
    O_2: predicate('network-isolated reconstruction #2 executed', offlineReasons(1))
  };
  const finalVerified = Object.values(predicates).every(item => item.value);
  const evidenceSha256 = createHash('sha256').update(JSON.stringify(evidence)).digest('hex');

  return {
    status: finalVerified ? 'FINAL VERIFIED — WORKFLOW EVIDENCE VALIDATED' : 'REJECTED — WORKFLOW EVIDENCE INCOMPLETE OR INVALID',
    formula: `C_final = ${predicates.P.value} AND ${predicates.T.value} AND ${predicates.E.value} AND ${predicates.O_1.value} AND ${predicates.O_2.value} = ${finalVerified}`,
    finalVerified,
    predicates,
    canonicalAnchors: CANONICAL_ANCHORS,
    evidenceSha256,
    evidenceSource,
    generatedAt: typeof (evidence as any).generatedAt === 'string' ? (evidence as any).generatedAt : null
  };
}

export function loadCertificationEvidence(filePath = process.env.CERTIFICATION_EVIDENCE_PATH): { evidence: unknown; source: string } {
  if (!filePath) return { evidence: null, source: 'CERTIFICATION_EVIDENCE_PATH is not configured' };
  const resolved = path.resolve(filePath);
  return { evidence: JSON.parse(readFileSync(resolved, 'utf8')), source: resolved };
}
