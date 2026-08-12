import { createHash } from 'node:crypto';
import profileDocument from './zeta23-profile.json';

const SHA256 = /^[0-9a-f]{64}$/;
const COMMIT = /^[0-9a-f]{40}$/;

interface PredicateResult {
  name: string;
  value: boolean;
  state: 'VERIFIED' | 'FAILED';
  reasons: string[];
}

interface CommandRecord {
  id?: string;
  command?: string;
  exitCode?: number;
  logFile?: string;
  logSha256?: string;
}

interface VerifiedPinFile {
  path: string;
  sha256: string;
  bytes: number;
}

interface VerifiedComparatorConfig {
  id: string;
  path: string;
  theoremCount: number;
  permittedAxioms: string[];
  enableNanoda: boolean;
}

export interface Zeta23VerificationContext {
  baseFinalVerified: boolean;
  baseAuthenticityVerified: boolean;
  baseProfileId: string;
  baseEvidenceSha256: string;
  workflowRepository: string;
  workflowCommit: string;
  workflowRunId: string;
  sourceCommit: string;
  sourceTreeSha256: string;
  sourceTrackedFilesClean: boolean;
  pinFiles: VerifiedPinFile[];
  comparatorConfigs: VerifiedComparatorConfig[];
  toolSourceCommits: Record<'comparator' | 'lean4export' | 'landrun' | 'nanoda', string>;
  toolTrackedFilesClean: Record<'comparator' | 'lean4export' | 'landrun' | 'nanoda', boolean>;
  binarySha256: Record<'lean' | 'lake' | 'comparator' | 'lean4export' | 'landrun' | 'nanoda', string>;
  logs: Record<string, string>;
}

export interface Zeta23Evaluation {
  status: string;
  coreFormula: string;
  strongFormula: string;
  coreVerified: boolean;
  strongVerified: boolean;
  pairCeiling: {
    verified: boolean;
    conditionalOn: string;
    reasons: string[];
  };
  predicates: Record<string, PredicateResult>;
  profileId: string;
  evidenceSha256: string | null;
}

function get(record: unknown, keys: string[]): any {
  let current = record as any;
  for (const key of keys) current = current && typeof current === 'object' ? current[key] : undefined;
  return current;
}

function predicate(name: string, reasons: string[]): PredicateResult {
  return { name, value: reasons.length === 0, state: reasons.length === 0 ? 'VERIFIED' : 'FAILED', reasons };
}

function arraysEqual(left: unknown, right: unknown): boolean {
  return Array.isArray(left) && Array.isArray(right)
    && left.length === right.length
    && left.every((value, index) => value === right[index]);
}

function sameSet(left: unknown, right: unknown): boolean {
  return Array.isArray(left) && Array.isArray(right)
    && left.length === right.length
    && [...left].sort().every((value, index) => value === [...right].sort()[index]);
}

function commandLog(record: CommandRecord | undefined, context: Zeta23VerificationContext, reasons: string[]): string {
  if (!record || typeof record.logFile !== 'string' || !record.logFile || record.logFile.includes('..')) {
    reasons.push(`Command ${record?.id || '<unknown>'} has an invalid log path.`);
    return '';
  }
  const contents = context.logs[record.logFile];
  if (typeof contents !== 'string') {
    reasons.push(`Command ${record.id || '<unknown>'} log is unavailable.`);
    return '';
  }
  const actualHash = createHash('sha256').update(contents).digest('hex');
  if (!SHA256.test(String(record.logSha256 || '')) || record.logSha256 !== actualHash) {
    reasons.push(`Command ${record.id || '<unknown>'} log hash does not match its bytes.`);
  }
  return contents;
}

function parseAxiomLines(contents: string): Map<string, string[]> {
  const result = new Map<string, string[]>();
  for (const line of contents.split(/\r?\n/)) {
    const depends = line.match(/^'([^']+)' depends on axioms: \[([^\]]*)\]$/);
    if (depends) {
      result.set(depends[1], result.has(depends[1])
        ? ['<duplicate axiom record>']
        : depends[2] ? depends[2].split(',').map(value => value.trim()) : []);
      continue;
    }
    const none = line.match(/^'([^']+)' does not depend on any axioms$/);
    if (none) result.set(none[1], result.has(none[1]) ? ['<duplicate axiom record>'] : []);
  }
  return result;
}

function validateRecordedCommand(
  record: CommandRecord | undefined,
  expected: { id: string; command: string },
  context: Zeta23VerificationContext,
  reasons: string[]
): string {
  if (!record) {
    reasons.push(`Command ${expected.id} is missing.`);
    return '';
  }
  if (record.id !== expected.id || record.command !== expected.command) {
    reasons.push(`Command ${expected.id} does not match its canonical definition.`);
  }
  if (record.exitCode !== 0) reasons.push(`Command ${expected.id} did not exit 0.`);
  return commandLog(record, context, reasons);
}

function validateAxiomAudit(
  contents: string,
  declarations: string[],
  expectedAxioms: string[],
  label: string,
  reasons: string[]
): void {
  const parsed = parseAxiomLines(contents);
  if (parsed.size !== declarations.length) reasons.push(`${label} printed ${parsed.size} axiom records; expected ${declarations.length}.`);
  for (const declaration of declarations) {
    const actual = parsed.get(declaration);
    if (!actual) reasons.push(`${label} is missing axiom output for ${declaration}.`);
    else if (!arraysEqual(actual, expectedAxioms)) reasons.push(`${declaration} has a non-canonical axiom set.`);
  }
}

export function evaluateZeta23Evidence(evidence: unknown, context: Zeta23VerificationContext): Zeta23Evaluation {
  if (!evidence || typeof evidence !== 'object') {
    const missing = predicate('required evidence is present', ['No Zeta23 workflow evidence was supplied.']);
    return {
      status: 'PENDING — ZETA23 EVIDENCE NOT LOADED',
      coreFormula: 'Z_core = T AND S AND B AND A = false',
      strongFormula: 'Z_strong = Z_core AND C_base AND C_multiplicity AND C_xiprime = false',
      coreVerified: false,
      strongVerified: false,
      pairCeiling: { verified: false, conditionalOn: profileDocument.pairCeilingAxiomAudit.conditionalOn, reasons: missing.reasons },
      predicates: { T: missing, S: missing, B: missing, A: missing, C_base: missing, C_multiplicity: missing, C_xiprime: missing },
      profileId: profileDocument.profileId,
      evidenceSha256: null
    };
  }

  const transportReasons: string[] = [];
  const recordedBaseHash = get(evidence, ['toolchain', 'baseEvidenceSha256']);
  if (!context.baseFinalVerified) transportReasons.push('The underlying portable-toolchain evidence did not independently evaluate to FINAL VERIFIED.');
  if (!context.baseAuthenticityVerified) transportReasons.push('The underlying evidence and manifest attestations were not independently verified by the final evaluator.');
  if (context.baseProfileId !== profileDocument.requiredToolchainProfile) transportReasons.push('The underlying certificate is not the required rc2 profile.');
  if (!SHA256.test(context.baseEvidenceSha256) || recordedBaseHash !== context.baseEvidenceSha256) transportReasons.push('The underlying evidence hash is missing or does not match the authenticated bytes.');
  if (get(evidence, ['toolchain', 'profileId']) !== profileDocument.requiredToolchainProfile) transportReasons.push('The Zeta evidence names the wrong portable-toolchain profile.');
  if (get(evidence, ['toolchain', 'factory', 'repository']) !== context.workflowRepository
    || get(evidence, ['toolchain', 'factory', 'commit']) !== context.workflowCommit
    || String(get(evidence, ['toolchain', 'factory', 'runId']) || '') !== context.workflowRunId) {
    transportReasons.push('The Zeta receipt is not bound to the active factory repository, commit, and workflow run.');
  }
  const reconstruction = get(evidence, ['toolchain', 'reconstruction']) as CommandRecord | undefined;
  if (reconstruction?.id !== 'toolchain-reconstruction' || reconstruction?.exitCode !== 0) transportReasons.push('Portable-toolchain reconstruction did not exit 0.');
  commandLog(reconstruction, context, transportReasons);
  if (get(evidence, ['toolchain', 'networkMode']) !== 'none') transportReasons.push('Zeta core execution was not recorded with networkMode=none.');
  for (const binary of ['lean', 'lake']) {
    const recorded = String(get(evidence, ['toolchain', 'binaries', binary, 'sha256']) || '');
    if (!SHA256.test(recorded) || recorded !== context.binarySha256[binary as 'lean' | 'lake']) {
      transportReasons.push(`${binary} executable SHA-256 does not match the executed binary.`);
    }
  }
  const authenticationRecords = get(evidence, ['toolchain', 'authentication']);
  for (const id of ['base-evidence-attestation', 'toolchain-manifest-attestation', 'base-evidence-evaluation']) {
    const record = Array.isArray(authenticationRecords)
      ? authenticationRecords.find((candidate: CommandRecord) => candidate?.id === id)
      : undefined;
    if (!record) {
      transportReasons.push(`Toolchain authentication record ${id} is missing.`);
      continue;
    }
    if (record.exitCode !== 0) transportReasons.push(`Toolchain authentication record ${id} did not exit 0.`);
    commandLog(record, context, transportReasons);
  }

  const sourceReasons: string[] = [];
  if (get(evidence, ['schemaVersion']) !== '1.0.0') sourceReasons.push('Zeta evidence schemaVersion must be 1.0.0.');
  if (get(evidence, ['profileId']) !== profileDocument.profileId) sourceReasons.push('Zeta evidence profileId is not allow-listed.');
  if (get(evidence, ['source', 'repository']) !== profileDocument.source.repository) sourceReasons.push('Zeta source repository identity is invalid.');
  if (get(evidence, ['source', 'commit']) !== profileDocument.source.commit || context.sourceCommit !== profileDocument.source.commit) sourceReasons.push('Zeta source commit does not match the canonical commit.');
  if (!context.sourceTrackedFilesClean) sourceReasons.push('Zeta tracked source files changed after checkout.');
  if (!SHA256.test(String(get(evidence, ['source', 'treeSha256']) || '')) || get(evidence, ['source', 'treeSha256']) !== context.sourceTreeSha256) {
    sourceReasons.push('Zeta source-tree SHA-256 does not match the checked source bytes.');
  }
  for (const expected of profileDocument.pinFiles) {
    const actual = context.pinFiles.find(candidate => candidate.path === expected.path);
    if (!actual || actual.sha256 !== expected.sha256 || actual.bytes !== expected.bytes) sourceReasons.push(`Pinned source file ${expected.path} does not match its canonical bytes.`);
  }

  const coreReasons: string[] = [];
  const coreRecords = get(evidence, ['core', 'commands']);
  if (!Array.isArray(coreRecords)) {
    coreReasons.push('Zeta core command records are missing.');
  } else {
    const coreDefinitions = profileDocument.coreCommands.filter(command => !command.id.startsWith('axioms-'));
    for (const definition of coreDefinitions) {
      const record = coreRecords.find((candidate: CommandRecord) => candidate?.id === definition.id);
      const contents = validateRecordedCommand(record, definition, context, coreReasons);
      if (definition.id === 'lean-version' && !contents.includes('Lean (version 4.33.0-rc2')) coreReasons.push('Lean version output is not exactly the rc2 line.');
      if ((definition.id === 'lake-build' || definition.id === 'solution-build') && /declaration uses ['\"]sorry|sorryAx/i.test(contents)) {
        coreReasons.push(`${definition.id} emitted a forbidden sorry warning.`);
      }
    }
  }

  const axiomReasons: string[] = [];
  const axiomRecords = get(evidence, ['axioms', 'commands']);
  if (!Array.isArray(axiomRecords)) {
    axiomReasons.push('Headline axiom-audit records are missing.');
  } else {
    for (const audit of profileDocument.headlineAxiomAudits) {
      const definition = profileDocument.coreCommands.find(command => command.id === audit.id)!;
      const record = axiomRecords.find((candidate: CommandRecord) => candidate?.id === audit.id);
      const contents = validateRecordedCommand(record, definition, context, axiomReasons);
      validateAxiomAudit(contents, audit.declarations, profileDocument.standardAxioms, audit.id, axiomReasons);
    }
  }

  const pairReasons: string[] = [];
  const pairDefinition = profileDocument.coreCommands.find(command => command.id === profileDocument.pairCeilingAxiomAudit.id)!;
  const pairRecord = Array.isArray(axiomRecords)
    ? axiomRecords.find((candidate: CommandRecord) => candidate?.id === pairDefinition.id)
    : undefined;
  const pairContents = validateRecordedCommand(pairRecord, pairDefinition, context, pairReasons);
  const pairParsed = parseAxiomLines(pairContents);
  const pair = profileDocument.pairCeilingAxiomAudit;
  if (pairParsed.size !== 11) pairReasons.push(`PairCeiling printed ${pairParsed.size} axiom records; expected 11.`);
  for (const declaration of pair.standardDeclarations) {
    if (!arraysEqual(pairParsed.get(declaration), profileDocument.standardAxioms)) pairReasons.push(`${declaration} has a non-canonical axiom set.`);
  }
  if (!arraysEqual(pairParsed.get(pair.propextOnlyDeclaration), ['propext'])) pairReasons.push(`${pair.propextOnlyDeclaration} must depend only on propext.`);
  if (!arraysEqual(pairParsed.get(pair.axiomFreeDeclaration), [])) pairReasons.push(`${pair.axiomFreeDeclaration} must be axiom-free.`);

  const toolingReasons: string[] = [];
  for (const [name, expectedPin] of Object.entries(profileDocument.comparator.pins)) {
    if (get(evidence, ['comparatorTooling', 'pins', name]) !== expectedPin) toolingReasons.push(`${name} source pin is not canonical.`);
    if (context.toolSourceCommits[name as 'comparator' | 'lean4export' | 'landrun' | 'nanoda'] !== expectedPin
      || !context.toolTrackedFilesClean[name as 'comparator' | 'lean4export' | 'landrun' | 'nanoda']) {
      toolingReasons.push(`${name} executed from a modified or non-canonical source checkout.`);
    }
    const recorded = String(get(evidence, ['comparatorTooling', 'binaries', name, 'sha256']) || '');
    if (!SHA256.test(recorded) || recorded !== context.binarySha256[name as 'comparator' | 'lean4export' | 'landrun' | 'nanoda']) {
      toolingReasons.push(`${name} binary SHA-256 does not match the executed binary.`);
    }
  }
  const probeRecords = get(evidence, ['sandbox', 'probes']);
  if (!Array.isArray(probeRecords)) {
    toolingReasons.push('Sandbox probe records are missing.');
  } else {
    const landrun = probeRecords.find((candidate: CommandRecord) => candidate?.id === 'landrun-enforcement');
    const landrunLog = commandLog(landrun, context, toolingReasons);
    if (landrun?.exitCode !== 0 || !landrunLog.includes('LANDRUN_PROBE_PASS')) toolingReasons.push('The real-landrun write-denial probe did not pass.');
    const systemd = probeRecords.find((candidate: CommandRecord) => candidate?.id === 'systemd-user-scope');
    const systemdLog = commandLog(systemd, context, toolingReasons);
    if (systemd?.exitCode !== 0 || !systemdLog.includes('SYSTEMD_USER_SCOPE_PASS')) toolingReasons.push('The documented unprivileged systemd-run boundary did not pass.');
  }

  const comparatorRecords = get(evidence, ['comparators']);
  const comparatorPredicates: Record<string, PredicateResult> = {};
  for (const expected of profileDocument.comparator.configs) {
    const reasons = [...toolingReasons];
    const verifiedConfig = context.comparatorConfigs.find(candidate => candidate.id === expected.id);
    if (!verifiedConfig
      || verifiedConfig.path !== expected.path
      || verifiedConfig.theoremCount !== expected.theoremCount
      || !sameSet(verifiedConfig.permittedAxioms, profileDocument.comparator.permittedAxioms)
      || verifiedConfig.enableNanoda !== true) {
      reasons.push(`Comparator configuration ${expected.id} does not match the source-owned definition.`);
    }
    const record = Array.isArray(comparatorRecords) ? comparatorRecords.find((candidate: any) => candidate?.id === expected.id) : undefined;
    if (!record) {
      reasons.push(`Comparator run ${expected.id} is missing.`);
    } else {
      if (record.configPath !== expected.path) reasons.push(`Comparator run ${expected.id} used the wrong configuration.`);
      if (record.exitCode !== 0) reasons.push(`Comparator run ${expected.id} did not exit 0.`);
      if (record.preexistingSolutionArtifactCount !== 0) reasons.push(`Comparator run ${expected.id} did not start from a fresh Solution build state.`);
      if (record.landrunMode !== 'real' || record.systemdUserScope !== true || record.nanodaEnabled !== true) reasons.push(`Comparator run ${expected.id} did not use the required real landrun, systemd, and nanoda boundaries.`);
      if (!SHA256.test(String(record.sourceTreeSha256 || '')) || record.sourceTreeSha256 !== get(evidence, ['source', 'treeSha256'])) reasons.push(`Comparator run ${expected.id} did not use the canonical fresh source tree.`);
      const contents = commandLog(record, context, reasons);
      if (!contents.includes(profileDocument.comparator.successMessage)) reasons.push(`Comparator run ${expected.id} lacks the canonical success receipt.`);
    }
    comparatorPredicates[`C_${expected.id}`] = predicate(`fresh real-landrun + Lean-kernel + nanoda comparator (${expected.id})`, reasons);
  }

  const predicates: Record<string, PredicateResult> = {
    T: predicate('authenticated rc2 portable toolchain reconstructed with no network', transportReasons),
    S: predicate('exact Zeta23 source and pin files verified', sourceReasons),
    B: predicate('Zeta23 and all Solution targets built with no forbidden sorry warnings', coreReasons),
    A: predicate('33 headline declarations have exactly the standard three axioms', axiomReasons),
    ...comparatorPredicates
  };
  const coreVerified = predicates.T.value && predicates.S.value && predicates.B.value && predicates.A.value;
  const strongVerified = coreVerified && profileDocument.comparator.configs.every(config => predicates[`C_${config.id}`].value);
  const pairVerified = pairReasons.length === 0;
  const evidenceSha256 = createHash('sha256').update(JSON.stringify(evidence)).digest('hex');

  return {
    status: strongVerified
      ? 'ZETA23 STRONG VERIFIED — EXACT SOURCE, LEAN KERNEL, REAL LANDRUN, AND NANODA'
      : coreVerified
        ? 'ZETA23 CORE VERIFIED — STRONG COMPARATOR LAYER NOT VERIFIED'
        : 'REJECTED — ZETA23 EVIDENCE INCOMPLETE OR INVALID',
    coreFormula: `Z_core = ${predicates.T.value} AND ${predicates.S.value} AND ${predicates.B.value} AND ${predicates.A.value} = ${coreVerified}`,
    strongFormula: `Z_strong = ${coreVerified} AND ${predicates.C_base.value} AND ${predicates.C_multiplicity.value} AND ${predicates.C_xiprime.value} = ${strongVerified}`,
    coreVerified,
    strongVerified,
    pairCeiling: { verified: pairVerified, conditionalOn: pair.conditionalOn, reasons: pairReasons },
    predicates,
    profileId: profileDocument.profileId,
    evidenceSha256
  };
}

export const ZETA23_PROFILE = Object.freeze(profileDocument);
