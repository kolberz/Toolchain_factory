import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import test from 'node:test';
import {
  evaluateZeta23Evidence,
  ZETA23_PROFILE,
  type Zeta23VerificationContext
} from '../zeta23-certification.ts';

const sha = (character: string) => character.repeat(64);

function fixture(): { evidence: any; context: Zeta23VerificationContext } {
  const logs: Record<string, string> = {};
  const record = (id: string, command: string, contents: string): any => {
    const logFile = `${id}.log`;
    logs[logFile] = contents;
    return { id, command, exitCode: 0, logFile, logSha256: createHash('sha256').update(contents).digest('hex') };
  };
  const authentication = [
    record('base-evidence-attestation', '', 'attestation verified\n'),
    record('toolchain-manifest-attestation', '', 'attestation verified\n'),
    record('base-evidence-evaluation', '', 'FINAL VERIFIED\n')
  ];
  const reconstruction = record('toolchain-reconstruction', '', 'all archive parts verified\nreconstruction complete\n');
  const core = [
    record('lean-version', 'lean --version', 'Lean (version 4.33.0-rc2, x86_64-unknown-linux-gnu, Release)\n'),
    record('lake-build', 'lake build', 'Build completed successfully.\n'),
    record('solution-build', 'lake build Solution Solution.Multiplicity Solution.XiPrime', 'Build completed successfully.\n')
  ];
  const standardLine = (declaration: string) => `'${declaration}' depends on axioms: [${ZETA23_PROFILE.standardAxioms.join(', ')}]`;
  const axioms = ZETA23_PROFILE.headlineAxiomAudits.map(audit => {
    const definition = ZETA23_PROFILE.coreCommands.find(command => command.id === audit.id)!;
    return record(audit.id, definition.command, `${audit.declarations.map(standardLine).join('\n')}\n`);
  });
  const pair = ZETA23_PROFILE.pairCeilingAxiomAudit;
  const pairDefinition = ZETA23_PROFILE.coreCommands.find(command => command.id === pair.id)!;
  const pairLog = [
    ...pair.standardDeclarations.map(standardLine),
    `'${pair.propextOnlyDeclaration}' depends on axioms: [propext]`,
    `'${pair.axiomFreeDeclaration}' does not depend on any axioms`
  ].join('\n') + '\n';
  axioms.push(record(pair.id, pairDefinition.command, pairLog));

  const probes = [
    record('landrun-enforcement', '', 'permission denied\nLANDRUN_PROBE_PASS\n'),
    record('systemd-user-scope', '', 'SYSTEMD_USER_SCOPE_PASS\n')
  ];
  const comparators = ZETA23_PROFILE.comparator.configs.map(config => ({
    ...record(`comparator-${config.id}`, '', `${ZETA23_PROFILE.comparator.successMessage}\n`),
    id: config.id,
    configPath: config.path,
    preexistingSolutionArtifactCount: 0,
    sourceTreeSha256: sha('2'),
    landrunMode: 'real',
    systemdUserScope: true,
    nanodaEnabled: true
  }));

  const evidence = {
    schemaVersion: '1.0.0',
    profileId: ZETA23_PROFILE.profileId,
    source: { repository: ZETA23_PROFILE.source.repository, commit: ZETA23_PROFILE.source.commit, treeSha256: sha('2') },
    toolchain: {
      profileId: ZETA23_PROFILE.requiredToolchainProfile,
      baseEvidenceSha256: sha('1'),
      factory: { repository: 'kolberz/Toolchain_factory', commit: 'a'.repeat(40), runId: '12345' },
      reconstruction,
      networkMode: 'none',
      binaries: { lean: { sha256: sha('3') }, lake: { sha256: sha('4') } },
      authentication
    },
    core: { commands: core },
    axioms: { commands: axioms },
    sandbox: { probes },
    comparatorTooling: {
      pins: { ...ZETA23_PROFILE.comparator.pins },
      binaries: Object.fromEntries(Object.keys(ZETA23_PROFILE.comparator.pins).map((name, index) => [name, { sha256: sha(String(index + 5)) }]))
    },
    comparators
  };
  const context: Zeta23VerificationContext = {
    baseFinalVerified: true,
    baseAuthenticityVerified: true,
    baseProfileId: ZETA23_PROFILE.requiredToolchainProfile,
    baseEvidenceSha256: sha('1'),
    workflowRepository: 'kolberz/Toolchain_factory',
    workflowCommit: 'a'.repeat(40),
    workflowRunId: '12345',
    sourceCommit: ZETA23_PROFILE.source.commit,
    sourceTreeSha256: sha('2'),
    sourceTrackedFilesClean: true,
    pinFiles: ZETA23_PROFILE.pinFiles.map(file => ({ ...file })),
    comparatorConfigs: ZETA23_PROFILE.comparator.configs.map(config => ({
      ...config,
      permittedAxioms: [...ZETA23_PROFILE.comparator.permittedAxioms],
      enableNanoda: true
    })),
    toolSourceCommits: { ...ZETA23_PROFILE.comparator.pins },
    toolTrackedFilesClean: { comparator: true, lean4export: true, landrun: true, nanoda: true },
    binarySha256: {
      lean: sha('3'),
      lake: sha('4'),
      comparator: sha('5'),
      lean4export: sha('6'),
      landrun: sha('7'),
      nanoda: sha('8')
    },
    logs
  };
  return { evidence, context };
}

test('derives Zeta23 strong verification from exact source, logs, and comparator receipts', () => {
  const { evidence, context } = fixture();
  const result = evaluateZeta23Evidence(evidence, context);
  assert.equal(result.coreVerified, true);
  assert.equal(result.strongVerified, true);
  assert.equal(result.pairCeiling.verified, true);
});

test('rejects client-supplied Zeta predicate booleans', () => {
  const { context } = fixture();
  const result = evaluateZeta23Evidence({ T: true, S: true, B: true, A: true, C_base: true }, context);
  assert.equal(result.strongVerified, false);
});

test('rejects a headline theorem with a widened axiom set', () => {
  const { evidence, context } = fixture();
  const record = evidence.axioms.commands.find((candidate: any) => candidate.id === 'axioms-base');
  context.logs[record.logFile] = context.logs[record.logFile].replace('Quot.sound]', 'Quot.sound, sorryAx]');
  record.logSha256 = createHash('sha256').update(context.logs[record.logFile]).digest('hex');
  const result = evaluateZeta23Evidence(evidence, context);
  assert.equal(result.predicates.A.value, false);
  assert.equal(result.strongVerified, false);
});

test('rejects a fake-landrun comparator receipt', () => {
  const { evidence, context } = fixture();
  evidence.comparators[0].landrunMode = 'fake';
  assert.equal(evaluateZeta23Evidence(evidence, context).strongVerified, false);
});

test('rejects a Zeta receipt bound to different base evidence bytes', () => {
  const { evidence, context } = fixture();
  evidence.toolchain.baseEvidenceSha256 = sha('9');
  const result = evaluateZeta23Evidence(evidence, context);
  assert.equal(result.predicates.T.value, false);
  assert.equal(result.strongVerified, false);
});

test('rejects structurally valid base evidence when attestation verification fails', () => {
  const { evidence, context } = fixture();
  context.baseAuthenticityVerified = false;
  const result = evaluateZeta23Evidence(evidence, context);
  assert.equal(result.predicates.T.value, false);
  assert.equal(result.strongVerified, false);
});

test('rejects a comparator log whose bytes do not match the recorded hash', () => {
  const { evidence, context } = fixture();
  const record = evidence.comparators[1];
  context.logs[record.logFile] = 'tampered comparator output\n';
  assert.equal(evaluateZeta23Evidence(evidence, context).strongVerified, false);
});

test('rejects a substituted comparator binary', () => {
  const { evidence, context } = fixture();
  evidence.comparatorTooling.binaries.comparator.sha256 = sha('9');
  assert.equal(evaluateZeta23Evidence(evidence, context).strongVerified, false);
});

test('rejects a source-tree digest that was not recomputed from the checkout', () => {
  const { evidence, context } = fixture();
  evidence.source.treeSha256 = sha('9');
  assert.equal(evaluateZeta23Evidence(evidence, context).strongVerified, false);
});

test('keeps the EnclOK-conditional PairCeiling audit outside the unconditional strong formula', () => {
  const { evidence, context } = fixture();
  const record = evidence.axioms.commands.find((candidate: any) => candidate.id === 'axioms-pair-ceiling');
  context.logs[record.logFile] = context.logs[record.logFile].replace("'Zeta23.PairCeiling.LawN256_edge' does not depend on any axioms", "'Zeta23.PairCeiling.LawN256_edge' depends on axioms: [propext]");
  record.logSha256 = createHash('sha256').update(context.logs[record.logFile]).digest('hex');
  const result = evaluateZeta23Evidence(evidence, context);
  assert.equal(result.strongVerified, true);
  assert.equal(result.pairCeiling.verified, false);
  assert.equal(result.pairCeiling.conditionalOn, 'EnclOK');
});
