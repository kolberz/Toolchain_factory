import express from 'express';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import path from 'node:path';
import { readFileSync } from 'node:fs';
import { createServer as createViteServer } from 'vite';
import { GoogleGenAI } from '@google/genai';
import {
  CANONICAL_ANCHORS,
  CANONICAL_PROFILES,
  DEFAULT_PROFILE_ID,
  GATE_DEFINITIONS,
  evaluateCertificationEvidence,
  loadCertificationEvidence
} from './certification.ts';
import {
  evaluateProjectCertificationEvidence,
  loadProjectCertificationEvidence,
  type VerifiedToolchainContext
} from './project-certification.ts';

const ATTESTATION_REPOSITORY = 'kolberz/Toolchain_factory';
const ATTESTATION_WORKFLOW = 'kolberz/Toolchain_factory/.github/workflows/build-portable-toolchain.yml';

interface AttestationVerification {
  verified: boolean;
  repository: string;
  signerWorkflow: string;
  sourceDigest: string | null;
  sourceRef: string;
  evidenceSha256: string | null;
  message: string;
}

interface AttestationPolicy {
  repository: string;
  signerWorkflow: string;
  sourceRef: string;
  requireDeclaredWorkflow?: boolean;
}

const attestationCache = new Map<string, AttestationVerification>();

function verifyEvidenceAttestation(evidence: any, evidencePath: string, policy: AttestationPolicy): AttestationVerification {
  const sourceDigest = typeof evidence?.source?.commit === 'string' ? evidence.source.commit : null;
  const base = {
    repository: policy.repository,
    signerWorkflow: policy.signerWorkflow,
    sourceDigest,
    sourceRef: policy.sourceRef
  };

  if (!sourceDigest || !/^[0-9a-f]{40}$/.test(sourceDigest)) {
    return { ...base, verified: false, evidenceSha256: null, message: 'Evidence source commit is missing or invalid.' };
  }
  if (evidence?.source?.repository !== policy.repository) {
    return { ...base, verified: false, evidenceSha256: null, message: 'Evidence source repository does not match the attestation policy.' };
  }
  if (policy.requireDeclaredWorkflow && evidence?.source?.workflow !== policy.signerWorkflow) {
    return { ...base, verified: false, evidenceSha256: null, message: 'Evidence signer workflow does not match the attestation policy.' };
  }

  let rawEvidence: Buffer;
  try {
    rawEvidence = readFileSync(evidencePath);
  } catch (error: any) {
    return { ...base, verified: false, evidenceSha256: null, message: error?.message || 'Unable to read evidence bytes.' };
  }
  const evidenceSha256 = createHash('sha256').update(rawEvidence).digest('hex');
  const cacheKey = `${evidencePath}\0${evidenceSha256}\0${sourceDigest}\0${policy.sourceRef}\0${policy.repository}\0${policy.signerWorkflow}`;
  const cached = attestationCache.get(cacheKey);
  if (cached) return cached;

  const ghBinary = process.env.GITHUB_CLI_PATH || 'gh';
  const verification = spawnSync(ghBinary, [
    'attestation', 'verify', evidencePath,
    '--repo', policy.repository,
    '--signer-workflow', policy.signerWorkflow,
    '--source-digest', sourceDigest,
    '--source-ref', policy.sourceRef,
    '--deny-self-hosted-runners'
  ], {
    encoding: 'utf8',
    timeout: 60_000,
    windowsHide: true
  });

  const diagnostic = [verification.error?.message, verification.stderr, verification.stdout]
    .filter(Boolean)
    .join(' ')
    .replace(/\s+/g, ' ')
    .trim();
  const result: AttestationVerification = verification.status === 0
    ? { ...base, verified: true, evidenceSha256, message: 'GitHub attestation verified.' }
    : {
        ...base,
        verified: false,
        evidenceSha256,
        message: diagnostic || `GitHub attestation verification exited ${verification.status ?? 'without a status'}.`
      };
  // Cache only cryptographic success. Authentication/network failures must be
  // retried on the next request rather than becoming sticky until restart.
  if (result.verified) attestationCache.set(cacheKey, result);
  return result;
}

function readServerEvidence() {
  try {
    const loaded = loadCertificationEvidence();
    if (!loaded.evidence) {
      return {
        evidence: loaded.evidence,
        evaluation: evaluateCertificationEvidence(loaded.evidence, loaded.source),
        attestation: null,
        loadError: null
      };
    }
    const attestation = verifyEvidenceAttestation(loaded.evidence, loaded.source, {
      repository: ATTESTATION_REPOSITORY,
      signerWorkflow: ATTESTATION_WORKFLOW,
      sourceRef: process.env.CERTIFICATION_SOURCE_REF || 'refs/heads/main'
    });
    const provenanceReasons = attestation.verified
      ? []
      : [`Evidence authenticity was not verified: ${attestation.message}`];
    return {
      evidence: loaded.evidence,
      evaluation: evaluateCertificationEvidence(loaded.evidence, loaded.source, { provenanceReasons }),
      attestation,
      loadError: null
    };
  } catch (error: any) {
    const source = process.env.CERTIFICATION_EVIDENCE_PATH || 'CERTIFICATION_EVIDENCE_PATH';
    return {
      evidence: null,
      evaluation: evaluateCertificationEvidence(null, source),
      attestation: null,
      loadError: error?.message || 'Unable to load certification evidence.'
    };
  }
}

function readProjectServerEvidence() {
  const toolchainResult = readServerEvidence();
  const toolchain: VerifiedToolchainContext = {
    finalVerified: toolchainResult.evaluation.finalVerified,
    attestationVerified: toolchainResult.attestation?.verified === true,
    canonicalProfileId: toolchainResult.evaluation.canonicalProfileId,
    evidenceSha256: toolchainResult.attestation?.evidenceSha256 || null
  };

  try {
    const loaded = loadProjectCertificationEvidence();
    if (!loaded.evidence) {
      return {
        evidence: loaded.evidence,
        evaluation: evaluateProjectCertificationEvidence(loaded.evidence, toolchain, loaded.source),
        attestation: null,
        loadError: null
      };
    }

    const repository = process.env.PROJECT_CERTIFICATION_REPOSITORY;
    const signerWorkflow = process.env.PROJECT_CERTIFICATION_WORKFLOW;
    if (!repository || !signerWorkflow) {
      const missing = [
        !repository ? 'PROJECT_CERTIFICATION_REPOSITORY' : null,
        !signerWorkflow ? 'PROJECT_CERTIFICATION_WORKFLOW' : null
      ].filter(Boolean).join(' and ');
      return {
        evidence: loaded.evidence,
        evaluation: evaluateProjectCertificationEvidence(loaded.evidence, toolchain, loaded.source, {
          authenticated: false,
          authenticationReasons: [`Project evidence authenticity cannot be checked until ${missing} is configured.`]
        }),
        attestation: null,
        loadError: null
      };
    }

    const attestation = verifyEvidenceAttestation(loaded.evidence, loaded.source, {
      repository,
      signerWorkflow,
      sourceRef: process.env.PROJECT_CERTIFICATION_SOURCE_REF || 'refs/heads/main',
      requireDeclaredWorkflow: true
    });
    const authenticationReasons = attestation.verified
      ? []
      : [`Project evidence authenticity was not verified: ${attestation.message}`];
    return {
      evidence: loaded.evidence,
      evaluation: evaluateProjectCertificationEvidence(loaded.evidence, toolchain, loaded.source, {
        authenticated: attestation.verified,
        authenticationReasons,
        rawEvidenceSha256: attestation.evidenceSha256
      }),
      attestation,
      loadError: null
    };
  } catch (error: any) {
    const source = process.env.PROJECT_CERTIFICATION_EVIDENCE_PATH || 'PROJECT_CERTIFICATION_EVIDENCE_PATH';
    return {
      evidence: null,
      evaluation: evaluateProjectCertificationEvidence(null, toolchain, source),
      attestation: null,
      loadError: error?.message || 'Unable to load project certification evidence.'
    };
  }
}

async function startServer() {
  const app = express();
  const port = Number(process.env.PORT || 3000);

  app.use(express.json({ limit: '1mb' }));

  app.get('/api/health', (_req, res) => {
    res.json({ status: 'ok', service: 'Toolchain Factory evidence verifier', timestamp: new Date().toISOString() });
  });

  app.get('/api/certification/status', (_req, res) => {
    const { evaluation, attestation, loadError } = readServerEvidence();
    res.json({
      ...evaluation,
      attestation,
      loadError,
      target: 'P AND T AND E AND O_1 AND O_2 AND R derived from GitHub Actions evidence',
      trustBoundary: 'The browser cannot assign predicates. The server requires a GitHub-attested workflow evidence file.',
      automaticInvalidationRule: 'Any missing, malformed, or mismatched dependency makes its predicate false.'
    });
  });

  app.get('/api/certification/evidence', (_req, res) => {
    const result = readServerEvidence();
    res.json({
      evaluation: result.evaluation,
      evidence: result.evidence,
      attestation: result.attestation,
      loadError: result.loadError,
      immutability: 'Evidence must have a GitHub attestation bound to the canonical workflow, source commit, and configured source ref; this API is read-only.'
    });
  });

  app.post('/api/certification/evaluate', (_req, res) => {
    res.status(405).json({
      error: 'CLIENT_PREDICATE_ASSIGNMENT_REJECTED',
      message: 'P, T, E, O_1, O_2, and R are derived only from the server-owned workflow evidence file.',
      statusEndpoint: '/api/certification/status'
    });
  });

  app.post('/api/certification/reset', (_req, res) => {
    res.status(405).json({
      error: 'CERTIFICATION_IS_READ_ONLY',
      message: 'Run the GitHub Actions workflow and configure CERTIFICATION_EVIDENCE_PATH to change evidence.'
    });
  });

  app.get('/api/project-certification/status', (_req, res) => {
    const { evaluation, attestation, loadError } = readProjectServerEvidence();
    res.json({
      ...evaluation,
      attestation,
      loadError,
      target: 'A AND C_toolchain AND K_Lean AND W_external AND N_Lean AND N_external derived from workflow evidence',
      trustBoundary: 'Lean certifies exact aggregation logic. A separate verifier checks numerical witnesses. Neither layer is represented as proving the other.',
      automaticInvalidationRule: 'Any missing, malformed, unauthenticated, or cross-hash-mismatched dependency makes its predicate false.'
    });
  });

  app.get('/api/project-certification/evidence', (_req, res) => {
    const result = readProjectServerEvidence();
    res.json({
      evaluation: result.evaluation,
      evidence: result.evidence,
      attestation: result.attestation,
      loadError: result.loadError,
      immutability: 'Project evidence must be GitHub-attested by the explicitly configured project repository, workflow, commit, and source ref; this API is read-only.'
    });
  });

  app.post('/api/project-certification/evaluate', (_req, res) => {
    res.status(405).json({
      error: 'CLIENT_PROJECT_CERTIFICATION_REJECTED',
      message: 'Project predicates are derived only from the server-owned, attested project evidence file and verified base-toolchain context.',
      statusEndpoint: '/api/project-certification/status'
    });
  });

  app.get('/api/certification/gates', (_req, res) => {
    res.json({
      gateStatusFormula: 'actualOutcome(exitCode) === expectedOutcome(server-owned gate definition)',
      gates: GATE_DEFINITIONS,
      resultsEndpoint: '/api/certification/evidence',
      note: 'Definitions contain no predetermined exit codes, output, or success hashes.'
    });
  });

  app.get('/api/manifest/anchors', (_req, res) => {
    res.json({ DEFAULT_PROFILE_ID, MANIFEST_ANCHORS: CANONICAL_ANCHORS, PROFILES: CANONICAL_PROFILES });
  });

  app.get('/api/toolchain/bootstrap', (_req, res) => {
    res.json({
      service: 'Portable Lean Toolchain GitHub Actions Contract',
      version: '3.1.0',
      workflow: '.github/workflows/build-portable-toolchain.yml',
      buildScript: 'scripts/build-portable-toolchain.sh',
      profileFile: 'toolchain-profiles.json',
      defaultProfile: DEFAULT_PROFILE_ID,
      availableProfiles: Object.keys(CANONICAL_PROFILES),
      artifactNamePattern: [
        'portable-lean-toolchain-transport-index',
        'portable-lean-toolchain-part-NNN (derived from part-sha256sums.txt)',
        'portable-lean-toolchain-verification'
      ],
      acquisitionScript: 'scripts/download-actions-artifacts.sh',
      wrapperConstraint: 'Each payload part is uploaded as its own Actions artifact below 450 MiB.',
      certificationStatus: '/api/certification/status',
      projectCertificationStatus: '/api/project-certification/status',
      statement: 'Build, download, execution, and offline reconstruction occur on the Ubuntu workflow runner, not in the browser.'
    });
  });

  app.get('/api/toolchain/manifest', (_req, res) => {
    const manifestPath = process.env.TOOLCHAIN_MANIFEST_PATH;
    if (!manifestPath) {
      res.status(404).json({
        error: 'WORKFLOW_MANIFEST_NOT_LOADED',
        message: 'Download toolchain-manifest.json from a successful workflow run and configure TOOLCHAIN_MANIFEST_PATH.'
      });
      return;
    }
    try {
      res.json(JSON.parse(readFileSync(path.resolve(manifestPath), 'utf8')));
    } catch (error: any) {
      res.status(500).json({ error: 'INVALID_WORKFLOW_MANIFEST', message: error?.message });
    }
  });

  for (const route of ['/api/toolchain/parts', '/api/toolchain/reconstruct', '/api/toolchain/self-test', '/api/agent/verify']) {
    app.all(route, (_req, res) => {
      res.status(501).json({
        error: 'BROWSER_SIMULATION_REMOVED',
        message: 'This operation requires the real Linux GitHub Actions executor. No success result is synthesized by this server.',
        workflow: '.github/workflows/build-portable-toolchain.yml'
      });
    });
  }

  app.get('/api/github/diagnostic', (_req, res) => {
    res.json({
      repository: 'kolberz/Toolchain_factory',
      status: 'REPOSITORY_TARGET_CONFIGURED',
      note: 'Runtime GitHub authorization is intentionally not inferred from application state.'
    });
  });

  app.post('/api/genai', async (req, res) => {
    try {
      const { prompt, systemInstruction } = req.body || {};
      const apiKey = process.env.GEMINI_API_KEY;
      if (!apiKey) {
        res.status(500).json({ error: 'GEMINI_API_KEY environment variable is missing on server.' });
        return;
      }
      const ai = new GoogleGenAI({ apiKey });
      const response = await ai.models.generateContent({
        model: 'gemini-2.5-flash',
        contents: prompt,
        config: systemInstruction ? { systemInstruction } : undefined
      });
      res.json({ text: response.text });
    } catch (error: any) {
      res.status(500).json({ error: error?.message || 'Failed to query AI server engine.' });
    }
  });

  if (process.env.NODE_ENV !== 'production') {
    const vite = await createViteServer({ server: { middlewareMode: true }, appType: 'spa' });
    app.use(vite.middlewares);
  } else {
    const distPath = path.join(process.cwd(), 'dist');
    app.use(express.static(distPath));
    app.get('*', (_req, res) => res.sendFile(path.join(distPath, 'index.html')));
  }

  app.listen(port, '0.0.0.0', () => console.log(`Backend server running on http://0.0.0.0:${port}`));
}

startServer();
