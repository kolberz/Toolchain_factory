import { ToolchainConfig, CompatibilityIssue } from '../types/toolchain';

export function validateToolchainConfig(config: ToolchainConfig): CompatibilityIssue[] {
  const issues: CompatibilityIssue[] = [];

  // Check 1: Vite 6 requires Node >= 18
  if (config.bundler === 'vite' && config.runtime === 'node22') {
    issues.push({
      id: 'vite6-node',
      severity: 'info',
      title: 'Optimal Node & Vite Alignment',
      description: 'Vite 6 runs natively on Node.js 22 LTS with full ES Module and top-level await support.',
      fixable: false,
    });
  }

  // Check 2: Bun runtime with Docker Multi-stage
  if (config.runtime === 'bun' && config.container === 'docker-multi') {
    issues.push({
      id: 'bun-docker-alpine',
      severity: 'warning',
      title: 'Bun Alpine Base Image Notice',
      description: 'Bun recommends oven/bun:1-alpine image tag for lightweight containerization.',
      fixable: true,
      fixAction: (cfg) => ({ ...cfg, container: 'docker-simple' }),
    });
  }

  // Check 3: Next.js 15 requires Turbopack or Webpack
  if (config.framework === 'next15' && config.bundler === 'vite') {
    issues.push({
      id: 'nextjs-vite-mismatch',
      severity: 'error',
      title: 'Next.js 15 Framework & Bundler Conflict',
      description: 'Next.js 15 uses Turbopack/Webpack internally. Vite cannot bundle Next.js App Router applications directly.',
      fixable: true,
      fixAction: (cfg) => ({ ...cfg, bundler: 'turbopack' }),
    });
  }

  // Check 4: Biome Linter + ESLint combined redundancy
  if (config.linter === 'biome') {
    issues.push({
      id: 'biome-speed',
      severity: 'info',
      title: 'Biome Rust Linter Enabled',
      description: 'Biome replaces both ESLint and Prettier into a single sub-10ms formatter/linter binary.',
      fixable: false,
    });
  }

  // Check 5: Tailwind CSS v4 Vite integration
  if (config.styling === 'tailwind4' && config.bundler === 'vite') {
    issues.push({
      id: 'tailwind4-vite-plugin',
      severity: 'info',
      title: 'Tailwind v4 Native Vite Plugin',
      description: 'Using @tailwindcss/vite 4.x which eliminates postCSS config requirements.',
      fixable: false,
    });
  }

  // Check 6: GitHub Actions & Docker container pairing
  if (config.cicd === 'github-actions' && config.container !== 'none') {
    issues.push({
      id: 'gha-docker-buildx',
      severity: 'info',
      title: 'Docker Buildx Pipeline Included',
      description: 'Your GitHub Actions workflow will automatically cache Docker layers using buildx and GitHub Cache storage.',
      fixable: false,
    });
  }

  // Check 7: No testing framework selected
  if (config.testing === 'none') {
    issues.push({
      id: 'no-tests-warning',
      severity: 'warning',
      title: 'No Automated Testing Framework Selected',
      description: 'It is highly recommended to include Vitest or Playwright for automated CI verification before deployment.',
      fixable: true,
      fixAction: (cfg) => ({ ...cfg, testing: 'vitest' }),
    });
  }

  return issues;
}
