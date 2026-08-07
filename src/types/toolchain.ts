export type Framework = 'react19' | 'vue3' | 'svelte5' | 'next15' | 'solid' | 'vanilla' | 'lean4-mathlib';
export type Runtime = 'node22' | 'bun' | 'deno' | 'lean4-lake';
export type Bundler = 'vite' | 'rspack' | 'turbopack' | 'esbuild' | 'tsup' | 'lake-build';
export type Language = 'typescript' | 'javascript' | 'lean';
export type Styling = 'tailwind4' | 'css-modules' | 'styled-components' | 'shadcn' | 'none';
export type Testing = 'vitest' | 'playwright' | 'jest' | 'cypress' | 'lean-check' | 'none';
export type Linter = 'eslint9' | 'biome' | 'prettier-only' | 'none';
export type Container = 'docker-multi' | 'docker-simple' | 'podman' | 'none';
export type CiCd = 'github-actions' | 'gitlab-ci' | 'circleci' | 'none';
export type Deployment = 'cloud-run' | 'vercel' | 'netlify' | 'aws-s3' | 'github-pages' | 'none';

export type ZipDependencyClassification =
  | 'SELF-CONTAINED'
  | 'TOOLCHAIN-DEPENDENT'
  | 'MATHLIB-DEPENDENT'
  | 'SOURCE PATCH'
  | 'DIAGNOSTIC';

export interface SmallZipUnit {
  id: string;
  title: string;
  filename: string;
  classification: ZipDependencyClassification;
  purpose: string;
  files: GeneratedFile[];
  requires: string[];
}

export interface DiagnosticCapsule {
  failingFiles: { name: string; content: string }[];
  compilerOutput: string;
  importsRequired: string[];
  suggestedFix?: string;
}

export interface ToolchainConfig {
  projectName: string;
  projectDescription: string;
  githubRepoUrl: string;
  framework: Framework;
  runtime: Runtime;
  bundler: Bundler;
  language: Language;
  styling: Styling;
  testing: Testing;
  linter: Linter;
  container: Container;
  cicd: CiCd;
  deployment: Deployment;
  includeEnvExample: boolean;
  includeDockerCompose: boolean;
  includeMakefile: boolean;
  includeSetupScript: boolean;
  includeReadmeBadges: boolean;
  // Lean 4 specific extensions
  leanVersion?: string;
  includeMathlib?: boolean;
}

export interface GeneratedFile {
  path: string;
  filename: string;
  language: string;
  content: string;
  description: string;
  zipClassification?: ZipDependencyClassification;
}

export interface CompatibilityIssue {
  id: string;
  severity: 'error' | 'warning' | 'info';
  title: string;
  description: string;
  fixable: boolean;
  fixAction?: (config: ToolchainConfig) => ToolchainConfig;
}

export interface PipelineStep {
  id: string;
  name: string;
  category: 'lint' | 'test' | 'build' | 'container' | 'deploy';
  command: string;
  estimatedTimeSec: number;
  status: 'idle' | 'running' | 'success' | 'failed';
  logOutput: string[];
}
