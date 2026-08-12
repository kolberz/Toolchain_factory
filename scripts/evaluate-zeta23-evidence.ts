import { createHash } from 'node:crypto';
import { execFileSync, spawnSync } from 'node:child_process';
import { lstatSync, readFileSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { evaluateCertificationEvidence } from '../certification.ts';
import { evaluateZeta23Evidence, ZETA23_PROFILE, type Zeta23VerificationContext } from '../zeta23-certification.ts';

const [evidencePath, baseEvidencePath, manifestPath, logsDirectory, sourceDirectory, portableDirectory, toolsDirectory, verdictPath] = process.argv.slice(2);
if (!evidencePath || !baseEvidencePath || !manifestPath || !logsDirectory || !sourceDirectory || !portableDirectory || !toolsDirectory || !verdictPath) {
  console.error('usage: tsx scripts/evaluate-zeta23-evidence.ts ZETA_EVIDENCE BASE_EVIDENCE MANIFEST LOGS_DIR ZETA_SOURCE PORTABLE_DIR TOOLS_DIR VERDICT_JSON');
  process.exit(64);
}

const rawEvidence = readFileSync(evidencePath);
const evidence = JSON.parse(rawEvidence.toString('utf8'));
const rawBaseEvidence = readFileSync(baseEvidencePath);
const baseEvidence = JSON.parse(rawBaseEvidence.toString('utf8'));
const baseEvaluation = evaluateCertificationEvidence(baseEvidence, baseEvidencePath);
const workflowRepository = process.env.GITHUB_REPOSITORY || '';
const workflowCommit = process.env.GITHUB_SHA || '';
const workflowRunId = process.env.GITHUB_RUN_ID || '';
const workflowRef = process.env.GITHUB_REF || '';
const signerWorkflow = `${workflowRepository}/.github/workflows/build-portable-toolchain.yml`;
const attestationArguments = (subjectPath: string) => [
  'attestation', 'verify', subjectPath,
  '--repo', workflowRepository,
  '--signer-workflow', signerWorkflow,
  '--source-digest', workflowCommit,
  '--source-ref', workflowRef,
  '--deny-self-hosted-runners'
];
const evidenceAttestation = workflowRepository && workflowCommit && workflowRunId && workflowRef
  ? spawnSync('gh', attestationArguments(baseEvidencePath), { encoding: 'utf8' })
  : { status: 1 };
const manifestAttestation = workflowRepository && workflowCommit && workflowRunId && workflowRef
  ? spawnSync('gh', attestationArguments(manifestPath), { encoding: 'utf8' })
  : { status: 1 };
const baseAuthenticityVerified = evidenceAttestation.status === 0
  && manifestAttestation.status === 0
  && baseEvidence?.source?.repository === workflowRepository
  && baseEvidence?.source?.commit === workflowCommit
  && String(baseEvidence?.source?.runId || '') === workflowRunId;

const sourceRoot = path.resolve(sourceDirectory);
const logRoot = path.resolve(logsDirectory);
const sourceCommit = execFileSync('git', ['-C', sourceRoot, 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim();
const trackedStatus = execFileSync('git', ['-C', sourceRoot, 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim();
const trackedFilesRaw = execFileSync('git', ['-C', sourceRoot, 'ls-files', '-z']);
const trackedFiles = trackedFilesRaw.toString('utf8').split('\0').filter(Boolean).sort((left, right) => Buffer.compare(Buffer.from(left), Buffer.from(right)));
const sourceInventory = trackedFiles.map(relativePath => {
  const filename = path.resolve(sourceRoot, relativePath);
  if (!filename.startsWith(`${sourceRoot}${path.sep}`)) throw new Error(`tracked file escapes source root: ${relativePath}`);
  if (lstatSync(filename).isSymbolicLink()) throw new Error(`tracked source symlink is not allowed: ${relativePath}`);
  return `${createHash('sha256').update(readFileSync(filename)).digest('hex')}  ${relativePath}\n`;
}).join('');
const sourceTreeSha256 = createHash('sha256').update(sourceInventory).digest('hex');

const pinFiles = ZETA23_PROFILE.pinFiles.map(expected => {
  const filename = path.resolve(sourceRoot, expected.path);
  if (!filename.startsWith(`${sourceRoot}${path.sep}`)) throw new Error(`pin file escapes source root: ${expected.path}`);
  const bytes = readFileSync(filename);
  return { path: expected.path, sha256: createHash('sha256').update(bytes).digest('hex'), bytes: statSync(filename).size };
});

const comparatorConfigs = ZETA23_PROFILE.comparator.configs.map(expected => {
  const filename = path.resolve(sourceRoot, expected.path);
  if (!filename.startsWith(`${sourceRoot}${path.sep}`)) throw new Error(`config escapes source root: ${expected.path}`);
  const config = JSON.parse(readFileSync(filename, 'utf8'));
  return {
    id: expected.id,
    path: expected.path,
    theoremCount: Array.isArray(config.theorem_names) ? config.theorem_names.length : -1,
    permittedAxioms: config.permitted_axioms,
    enableNanoda: config.enable_nanoda
  };
});

const records = [
  ...(Array.isArray(evidence?.toolchain?.authentication) ? evidence.toolchain.authentication : []),
  ...(evidence?.toolchain?.reconstruction ? [evidence.toolchain.reconstruction] : []),
  ...(Array.isArray(evidence?.core?.commands) ? evidence.core.commands : []),
  ...(Array.isArray(evidence?.axioms?.commands) ? evidence.axioms.commands : []),
  ...(Array.isArray(evidence?.sandbox?.probes) ? evidence.sandbox.probes : []),
  ...(Array.isArray(evidence?.comparators) ? evidence.comparators : [])
];
const logs: Record<string, string> = {};
for (const record of records) {
  if (typeof record?.logFile !== 'string' || record.logFile.includes('..')) continue;
  const filename = path.resolve(logRoot, record.logFile);
  if (!filename.startsWith(`${logRoot}${path.sep}`)) throw new Error(`log path escapes log root: ${record.logFile}`);
  logs[record.logFile] = readFileSync(filename, 'utf8');
}

const context: Zeta23VerificationContext = {
  baseFinalVerified: baseEvaluation.finalVerified,
  baseAuthenticityVerified,
  baseProfileId: baseEvaluation.canonicalProfileId,
  baseEvidenceSha256: createHash('sha256').update(rawBaseEvidence).digest('hex'),
  workflowRepository,
  workflowCommit,
  workflowRunId,
  sourceCommit,
  sourceTreeSha256,
  sourceTrackedFilesClean: trackedStatus === '',
  pinFiles,
  comparatorConfigs,
  toolSourceCommits: {
    comparator: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'comparator'), 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim(),
    lean4export: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'comparator/.lake/packages/lean4export'), 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim(),
    landrun: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'landrun'), 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim(),
    nanoda: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'nanoda'), 'rev-parse', 'HEAD'], { encoding: 'utf8' }).trim()
  },
  toolTrackedFilesClean: {
    comparator: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'comparator'), 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim() === '',
    lean4export: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'comparator/.lake/packages/lean4export'), 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim() === '',
    landrun: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'landrun'), 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim() === '',
    nanoda: execFileSync('git', ['-C', path.resolve(toolsDirectory, 'nanoda'), 'status', '--porcelain', '--untracked-files=no'], { encoding: 'utf8' }).trim() === ''
  },
  binarySha256: {
    lean: createHash('sha256').update(readFileSync(path.resolve(portableDirectory, 'lean/bin/lean'))).digest('hex'),
    lake: createHash('sha256').update(readFileSync(path.resolve(portableDirectory, 'lean/bin/lake'))).digest('hex'),
    comparator: createHash('sha256').update(readFileSync(path.resolve(toolsDirectory, 'comparator/.lake/build/bin/comparator'))).digest('hex'),
    lean4export: createHash('sha256').update(readFileSync(path.resolve(toolsDirectory, 'comparator/.lake/packages/lean4export/.lake/build/bin/lean4export'))).digest('hex'),
    landrun: createHash('sha256').update(readFileSync(path.resolve(toolsDirectory, 'bin/landrun'))).digest('hex'),
    nanoda: createHash('sha256').update(readFileSync(path.resolve(toolsDirectory, 'nanoda/target/release/nanoda_bin'))).digest('hex')
  },
  logs
};
const evaluation = evaluateZeta23Evidence(evidence, context);
const verdict = {
  schemaVersion: '1.0.0',
  rawEvidenceSha256: createHash('sha256').update(rawEvidence).digest('hex'),
  baseEvidenceEvaluation: {
    rawEvidenceSha256: context.baseEvidenceSha256,
    canonicalProfileId: baseEvaluation.canonicalProfileId,
    finalVerified: baseEvaluation.finalVerified,
    authenticityVerified: baseAuthenticityVerified
  },
  ...evaluation
};

writeFileSync(verdictPath, `${JSON.stringify(verdict, null, 2)}\n`);
console.log(JSON.stringify(verdict, null, 2));
if (!evaluation.strongVerified) process.exit(1);
