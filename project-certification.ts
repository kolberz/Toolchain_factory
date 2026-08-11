import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { CANONICAL_PROFILES } from './certification.ts';

const SHA256 = /^[0-9a-f]{64}$/;
const COMMIT_SHA = /^[0-9a-f]{40}$/;

export type ProjectPredicateCode = 'A' | 'C_toolchain' | 'K_Lean' | 'W_external' | 'N_Lean' | 'N_external';

export interface ProjectPredicateResult {
  name: string;
  value: boolean;
  state: 'VERIFIED' | 'FAILED' | 'PENDING';
  reasons: string[];
}

export interface VerifiedToolchainContext {
  finalVerified: boolean;
  attestationVerified: boolean;
  canonicalProfileId: string | null;
  evidenceSha256: string | null;
}

export interface ProjectCertificationOptions {
  authenticated?: boolean;
  authenticationReasons?: string[];
  rawEvidenceSha256?: string | null;
}

export interface ProjectCertificationEvaluation {
  status: string;
  formula: string;
  semanticFormula: string;
  semanticVerified: boolean;
  finalVerified: boolean;
  predicates: Record<ProjectPredicateCode, ProjectPredicateResult>;
  projectId: string | null;
  projectRevision: string | null;
  componentCount: number | null;
  toolchainProfileId: string | null;
  toolchainEvidenceSha256: string | null;
  projectEvidenceSha256: string | null;
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

function isNonEmptyString(value: unknown): value is string {
  return typeof value === 'string' && value.trim().length > 0;
}

function predicate(name: string, reasons: string[], pending = false): ProjectPredicateResult {
  return {
    name,
    value: reasons.length === 0 && !pending,
    state: pending ? 'PENDING' : reasons.length === 0 ? 'VERIFIED' : 'FAILED',
    reasons
  };
}

function pendingEvaluation(evidenceSource: string): ProjectCertificationEvaluation {
  const pending = (name: string) => predicate(name, ['No project workflow evidence has been loaded.'], true);
  const predicates = {
    A: pending('project evidence is authenticated'),
    C_toolchain: pending('certified toolchain evidence is bound by hash'),
    K_Lean: pending('Lean kernel checked the project aggregation'),
    W_external: pending('independent verifier checked every numerical witness'),
    N_Lean: pending('malformed Lean aggregation was rejected'),
    N_external: pending('mutated numerical witness was rejected')
  };
  return {
    status: 'PENDING — PROJECT EVIDENCE NOT LOADED',
    formula: 'C_project = A AND C_toolchain AND K_Lean AND W_external AND N_Lean AND N_external = false',
    semanticFormula: 'C_semantic = C_toolchain AND K_Lean AND W_external AND N_Lean AND N_external = false',
    semanticVerified: false,
    finalVerified: false,
    predicates,
    projectId: null,
    projectRevision: null,
    componentCount: null,
    toolchainProfileId: null,
    toolchainEvidenceSha256: null,
    projectEvidenceSha256: null,
    evidenceSource,
    generatedAt: null
  };
}

export function evaluateProjectCertificationEvidence(
  evidence: unknown,
  toolchain: VerifiedToolchainContext,
  evidenceSource = 'server-owned project evidence file',
  options: ProjectCertificationOptions = {}
): ProjectCertificationEvaluation {
  if (!evidence || typeof evidence !== 'object') return pendingEvaluation(evidenceSource);

  const authenticityReasons = [...(options.authenticationReasons || [])];
  if (options.authenticated !== true && authenticityReasons.length === 0) {
    authenticityReasons.push('Project evidence attestation has not been verified.');
  }
  if (get(evidence, ['schemaVersion']) !== '1.0.0') authenticityReasons.push('Project evidence schemaVersion must be 1.0.0.');
  if (!isNonEmptyString(get(evidence, ['source', 'repository']))) authenticityReasons.push('Project source repository is missing.');
  if (!COMMIT_SHA.test(String(get(evidence, ['source', 'commit']) || ''))) authenticityReasons.push('Project source commit SHA is invalid.');
  if (!/^[0-9]+$/.test(String(get(evidence, ['source', 'runId']) || ''))) authenticityReasons.push('Project workflow run ID is invalid.');
  if (!isNonEmptyString(get(evidence, ['source', 'workflow']))) authenticityReasons.push('Project signer workflow is missing.');
  if (!isNonEmptyString(get(evidence, ['source', 'runnerImage']))) authenticityReasons.push('Project runner image is missing.');

  const toolchainReasons: string[] = [];
  const evidenceProfileId = get(evidence, ['toolchain', 'profileId']);
  const evidenceToolchainSha = get(evidence, ['toolchain', 'certificationEvidenceSha256']);
  if (!toolchain.finalVerified) toolchainReasons.push('The referenced toolchain is not FINAL VERIFIED by the base evaluator.');
  if (!toolchain.attestationVerified) toolchainReasons.push('The referenced toolchain evidence attestation is not verified.');
  if (!isNonEmptyString(evidenceProfileId) || !CANONICAL_PROFILES[evidenceProfileId]) {
    toolchainReasons.push('The project toolchain profile is missing or is not allow-listed.');
  }
  if (evidenceProfileId !== toolchain.canonicalProfileId) toolchainReasons.push('The project toolchain profile does not match the server-verified toolchain.');
  if (!isSha256(evidenceToolchainSha)) toolchainReasons.push('The referenced toolchain evidence SHA-256 is invalid.');
  if (!isSha256(toolchain.evidenceSha256)) toolchainReasons.push('The server-verified toolchain evidence SHA-256 is unavailable.');
  if (evidenceToolchainSha !== toolchain.evidenceSha256) toolchainReasons.push('The project is bound to a different toolchain evidence file.');

  const projectId = get(evidence, ['project', 'id']);
  const projectRevision = get(evidence, ['project', 'revision']);
  const componentBankSha = get(evidence, ['project', 'componentBankSha256']);
  const componentCount = get(evidence, ['project', 'componentCount']);

  const leanReasons: string[] = [];
  if (!isNonEmptyString(projectId)) leanReasons.push('Project ID is missing.');
  if (!isNonEmptyString(projectRevision)) leanReasons.push('Project revision is missing.');
  if (!isNonEmptyString(get(evidence, ['leanAggregation', 'command']))) leanReasons.push('Lean aggregation command is missing.');
  if (!isNonEmptyString(get(evidence, ['leanAggregation', 'theorem']))) leanReasons.push('Lean aggregation theorem name is missing.');
  if (!isSha256(get(evidence, ['leanAggregation', 'sourceSha256']))) leanReasons.push('Lean aggregation source SHA-256 is invalid.');
  if (!isSha256(get(evidence, ['leanAggregation', 'leanExecutableSha256']))) leanReasons.push('Lean executable SHA-256 is invalid.');
  if (!isSha256(get(evidence, ['leanAggregation', 'logSha256']))) leanReasons.push('Lean aggregation log SHA-256 is invalid.');
  if (get(evidence, ['leanAggregation', 'exitCode']) !== 0) leanReasons.push('Lean aggregation did not exit 0.');
  if (!isNonEmptyString(get(evidence, ['leanAggregation', 'axiomsCommand']))) leanReasons.push('Lean axiom-audit command is missing.');
  if (!isSha256(get(evidence, ['leanAggregation', 'axiomsLogSha256']))) leanReasons.push('Lean axiom-audit log SHA-256 is invalid.');
  if (get(evidence, ['leanAggregation', 'axiomsExitCode']) !== 0) leanReasons.push('Lean axiom audit did not exit 0.');

  const externalReasons: string[] = [];
  if (!Number.isInteger(componentCount) || Number(componentCount) <= 0) externalReasons.push('Component count must be a positive integer.');
  if (!isSha256(componentBankSha)) externalReasons.push('Component-bank SHA-256 is invalid.');
  if (!isNonEmptyString(get(evidence, ['externalVerification', 'verifierName']))) externalReasons.push('External verifier name is missing.');
  if (!isNonEmptyString(get(evidence, ['externalVerification', 'verifierVersion']))) externalReasons.push('External verifier version is missing.');
  if (!isNonEmptyString(get(evidence, ['externalVerification', 'command']))) externalReasons.push('External verifier command is missing.');
  if (!isSha256(get(evidence, ['externalVerification', 'verifierExecutableSha256']))) externalReasons.push('External verifier executable SHA-256 is invalid.');
  if (!isSha256(get(evidence, ['externalVerification', 'numericPolicySha256']))) externalReasons.push('Numerical policy SHA-256 is invalid.');
  if (!isSha256(get(evidence, ['externalVerification', 'inputSha256']))) externalReasons.push('External verifier input SHA-256 is invalid.');
  if (get(evidence, ['externalVerification', 'inputSha256']) !== componentBankSha) externalReasons.push('External verifier input does not match the frozen component bank.');
  if (get(evidence, ['externalVerification', 'verifiedComponentCount']) !== componentCount) externalReasons.push('External verifier did not account for every frozen component.');
  if (get(evidence, ['externalVerification', 'exitCode']) !== 0) externalReasons.push('External witness verification did not exit 0.');
  if (!isSha256(get(evidence, ['externalVerification', 'logSha256']))) externalReasons.push('External verifier log SHA-256 is invalid.');

  const negativeReasons = (layer: 'lean' | 'external', positiveInput: unknown): string[] => {
    const reasons: string[] = [];
    const label = layer === 'lean' ? 'Lean' : 'external verifier';
    const record = get(evidence, ['negativeControls', layer]) as any;
    if (!record || typeof record !== 'object') return [`${label} negative control is missing.`];
    if (!isNonEmptyString(record.id)) reasons.push(`${label} negative-control ID is missing.`);
    if (!isNonEmptyString(record.command)) reasons.push(`${label} negative-control command is missing.`);
    if (!isSha256(record.mutatedInputSha256)) reasons.push(`${label} mutated-input SHA-256 is invalid.`);
    if (record.mutatedInputSha256 === positiveInput) reasons.push(`${label} negative control did not mutate its positive input.`);
    if (!Number.isInteger(record.exitCode) || record.exitCode === 0) reasons.push(`${label} negative control was not rejected with a nonzero exit code.`);
    if (!isSha256(record.logSha256)) reasons.push(`${label} negative-control log SHA-256 is invalid.`);
    return reasons;
  };

  const predicates = {
    A: predicate('project evidence is authenticated', authenticityReasons),
    C_toolchain: predicate('certified toolchain evidence is bound by hash', toolchainReasons),
    K_Lean: predicate('Lean kernel checked the project aggregation', leanReasons),
    W_external: predicate('independent verifier checked every numerical witness', externalReasons),
    N_Lean: predicate('malformed Lean aggregation was rejected', negativeReasons('lean', get(evidence, ['leanAggregation', 'sourceSha256']))),
    N_external: predicate('mutated numerical witness was rejected', negativeReasons('external', componentBankSha))
  };
  const semanticVerified = ['C_toolchain', 'K_Lean', 'W_external', 'N_Lean', 'N_external']
    .every(code => predicates[code as Exclude<ProjectPredicateCode, 'A'>].value);
  const finalVerified = predicates.A.value && semanticVerified;
  const projectEvidenceSha256 = isSha256(options.rawEvidenceSha256)
    ? options.rawEvidenceSha256
    : createHash('sha256').update(JSON.stringify(evidence)).digest('hex');

  return {
    status: finalVerified
      ? 'PROJECT FINAL VERIFIED — TWO-LAYER EVIDENCE VALIDATED'
      : semanticVerified
        ? 'SEMANTICALLY VERIFIED — PROJECT ATTESTATION REQUIRED'
        : 'REJECTED — PROJECT EVIDENCE INCOMPLETE OR INVALID',
    formula: `C_project = ${predicates.A.value} AND ${predicates.C_toolchain.value} AND ${predicates.K_Lean.value} AND ${predicates.W_external.value} AND ${predicates.N_Lean.value} AND ${predicates.N_external.value} = ${finalVerified}`,
    semanticFormula: `C_semantic = ${predicates.C_toolchain.value} AND ${predicates.K_Lean.value} AND ${predicates.W_external.value} AND ${predicates.N_Lean.value} AND ${predicates.N_external.value} = ${semanticVerified}`,
    semanticVerified,
    finalVerified,
    predicates,
    projectId: isNonEmptyString(projectId) ? projectId : null,
    projectRevision: isNonEmptyString(projectRevision) ? projectRevision : null,
    componentCount: Number.isInteger(componentCount) ? Number(componentCount) : null,
    toolchainProfileId: isNonEmptyString(evidenceProfileId) ? evidenceProfileId : null,
    toolchainEvidenceSha256: isSha256(evidenceToolchainSha) ? evidenceToolchainSha : null,
    projectEvidenceSha256,
    evidenceSource,
    generatedAt: isNonEmptyString(get(evidence, ['generatedAt'])) ? String(get(evidence, ['generatedAt'])) : null
  };
}

export function loadProjectCertificationEvidence(filePath = process.env.PROJECT_CERTIFICATION_EVIDENCE_PATH): { evidence: unknown; source: string } {
  if (!filePath) return { evidence: null, source: 'PROJECT_CERTIFICATION_EVIDENCE_PATH is not configured' };
  const resolved = path.resolve(filePath);
  return { evidence: JSON.parse(readFileSync(resolved, 'utf8')), source: resolved };
}
