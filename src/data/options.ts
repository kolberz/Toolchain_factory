import {
  Framework, Runtime, Bundler, Language, Styling,
  Testing, Linter, Container, CiCd, Deployment
} from '../types/toolchain';

export interface OptionItem<T> {
  id: T;
  name: string;
  category: string;
  description: string;
  icon: string;
  popular?: boolean;
  recommendedFor?: string;
  tags: string[];
}

export const FRAMEWORK_OPTIONS: OptionItem<Framework>[] = [
  { id: 'react19', name: 'React 19', category: 'Framework', description: 'Latest React with Server Actions & Concurrent Mode', icon: 'Atom', popular: true, tags: ['UI', 'Hooks', 'Vite'] },
  { id: 'lean4-mathlib', name: 'Lean 4 + Mathlib', category: 'Framework', description: 'Interactive theorem prover & formal verification suite with Mathlib', icon: 'ShieldCheck', popular: true, tags: ['Formal AI', 'Proofs', 'Mathlib'] },
  { id: 'vue3', name: 'Vue 3.5', category: 'Framework', description: 'Composition API, Vapor mode & Reactivity', icon: 'Code', tags: ['Reactivity', 'Single File Comp'] },
  { id: 'svelte5', name: 'Svelte 5', category: 'Framework', description: 'Runes reactivity system with zero runtime overhead', icon: 'Sparkles', tags: ['Runes', 'No Virtual DOM'] },
  { id: 'next15', name: 'Next.js 15', category: 'Framework', description: 'React Server Components & App Router', icon: 'Server', popular: true, tags: ['SSR', 'Fullstack', 'RSC'] },
  { id: 'solid', name: 'Solid JS', category: 'Framework', description: 'Fine-grained reactive primitive rendering', icon: 'Activity', tags: ['Performance', 'Signals'] },
  { id: 'vanilla', name: 'Vanilla / SDK', category: 'Framework', description: 'Plain TypeScript / SDK library module without UI framework', icon: 'Box', tags: ['Library', 'NPM'] },
];

export const RUNTIME_OPTIONS: OptionItem<Runtime>[] = [
  { id: 'node22', name: 'Node.js 22 LTS', category: 'Runtime', description: 'Standard battle-tested JavaScript runtime with V8 engine', icon: 'Terminal', popular: true, tags: ['LTS', 'ESM'] },
  { id: 'lean4-lake', name: 'Lean 4 / Lake', category: 'Runtime', description: 'Official Lean 4 runtime and Lake build tool package manager', icon: 'Shield', popular: true, tags: ['Lean 4', 'Lake'] },
  { id: 'bun', name: 'Bun 1.2', category: 'Runtime', description: 'Ultra-fast all-in-one JS/TS package manager & runtime', icon: 'Flame', popular: true, tags: ['Fast', 'Built-in TS'] },
  { id: 'deno', name: 'Deno 2.0', category: 'Runtime', description: 'Secure TypeScript runtime with native npm package support', icon: 'Shield', tags: ['Secure', 'TypeScript'] },
];

export const BUNDLER_OPTIONS: OptionItem<Bundler>[] = [
  { id: 'vite', name: 'Vite 6', category: 'Bundler', description: 'Lightning-fast ES module dev server & Rollup production build', icon: 'Zap', popular: true, tags: ['HMR', 'ESM', 'Plugins'] },
  { id: 'lake-build', name: 'Lake Build Engine', category: 'Bundler', description: 'Lean package manager and C/C++ backend artifact compiler', icon: 'Cpu', popular: true, tags: ['Lean 4', 'Lake'] },
  { id: 'rspack', name: 'Rspack', category: 'Bundler', description: 'High-performance Rust-based bundler with Webpack API compatibility', icon: 'Cpu', popular: true, tags: ['Rust', 'Webpack Compatible'] },
  { id: 'turbopack', name: 'Turbopack', category: 'Bundler', description: 'Rust-powered incremental bundler built for Next.js', icon: 'Zap', tags: ['Next.js', 'Rust'] },
  { id: 'esbuild', name: 'esbuild', category: 'Bundler', description: 'Extremely fast Go-based bundler and minifier', icon: 'Compass', tags: ['Go', 'Fast'] },
  { id: 'tsup', name: 'tsup', category: 'Bundler', description: 'Zero-config TypeScript library bundler powered by esbuild', icon: 'Box', tags: ['Libraries', 'CJS/ESM'] },
];

export const STYLING_OPTIONS: OptionItem<Styling>[] = [
  { id: 'tailwind4', name: 'Tailwind CSS v4', category: 'Styling', description: 'Utility-first CSS framework with Vite CSS engine', icon: 'Palette', popular: true, tags: ['CSS-first', 'Modern'] },
  { id: 'shadcn', name: 'Shadcn UI', category: 'Styling', description: 'Accessible re-usable component primitives with Tailwind CSS', icon: 'Layout', popular: true, tags: ['Radix', 'Tailwind'] },
  { id: 'css-modules', name: 'CSS Modules', category: 'Styling', description: 'Scoped CSS stylesheets with zero external runtime dependencies', icon: 'FileCode', tags: ['Scoped', 'Standard'] },
  { id: 'styled-components', name: 'Styled Components', category: 'Styling', description: 'CSS-in-JS library with dynamic props styling', icon: 'Scissors', tags: ['CSS-in-JS', 'Props'] },
];

export const TESTING_OPTIONS: OptionItem<Testing>[] = [
  { id: 'vitest', name: 'Vitest', category: 'Testing', description: 'Blazing fast unit & integration testing framework native to Vite', icon: 'CheckCircle2', popular: true, tags: ['Vite Native', 'Jest API'] },
  { id: 'playwright', name: 'Playwright', category: 'Testing', description: 'Reliable cross-browser end-to-end web testing by Microsoft', icon: 'Globe', popular: true, tags: ['E2E', 'Chromium/Firefox'] },
  { id: 'jest', name: 'Jest', category: 'Testing', description: 'Delightful JavaScript testing framework with mocking & coverage', icon: 'Award', tags: ['Classic', 'Snapshots'] },
  { id: 'cypress', name: 'Cypress', category: 'Testing', description: 'Interactive visual browser testing & component runner', icon: 'Eye', tags: ['Visual E2E', 'UI Runner'] },
  { id: 'none', name: 'No Test Framework', category: 'Testing', description: 'Skip testing setup in generator output', icon: 'Minus', tags: ['Minimal'] },
];

export const LINTER_OPTIONS: OptionItem<Linter>[] = [
  { id: 'eslint9', name: 'ESLint 9 (Flat Config)', category: 'Linter', description: 'Modern eslint.config.js pluggable JavaScript/TypeScript linter', icon: 'ShieldCheck', popular: true, tags: ['Flat Config', 'Standard'] },
  { id: 'biome', name: 'Biome', category: 'Linter', description: 'Rust-powered lightning fast linter, formatter, and import sorter', icon: 'Sparkles', popular: true, tags: ['Rust', 'Linter + Formatter'] },
  { id: 'prettier-only', name: 'Prettier Only', category: 'Linter', description: 'Code formatting without strict linter rules', icon: 'AlignLeft', tags: ['Formatting'] },
  { id: 'none', name: 'None', category: 'Linter', description: 'No linter/formatter config files', icon: 'Minus', tags: ['Minimal'] },
];

export const CONTAINER_OPTIONS: OptionItem<Container>[] = [
  { id: 'docker-multi', name: 'Docker Multi-stage', category: 'Container', description: 'Production-optimized minimal node Alpine image with build cache', icon: 'Container', popular: true, tags: ['Alpine', 'Layer Cache'] },
  { id: 'docker-simple', name: 'Docker Simple', category: 'Container', description: 'Straightforward Dockerfile for fast local development', icon: 'Box', tags: ['Dev Ready'] },
  { id: 'podman', name: 'Podman File', category: 'Container', description: 'Daemonless rootless container specification', icon: 'Shield', tags: ['Daemonless'] },
  { id: 'none', name: 'No Container', category: 'Container', description: 'Skip Docker container file generation', icon: 'Minus', tags: ['Native'] },
];

export const CICD_OPTIONS: OptionItem<CiCd>[] = [
  { id: 'github-actions', name: 'GitHub Actions', category: 'CI/CD', description: 'Automated CI/CD matrix workflow in .github/workflows/ci.yml', icon: 'GitBranch', popular: true, tags: ['Workflows', 'GitHub'] },
  { id: 'gitlab-ci', name: 'GitLab CI/CD', category: 'CI/CD', description: '.gitlab-ci.yml multi-stage pipeline configuration', icon: 'Gitlab', tags: ['GitLab', 'Pipeline'] },
  { id: 'circleci', name: 'CircleCI', category: 'CI/CD', description: '.circleci/config.yml setup with parallelism & caching', icon: 'Circle', tags: ['CircleCI', 'Orbs'] },
  { id: 'none', name: 'No CI Pipeline', category: 'CI/CD', description: 'Skip automated CI/CD workflow files', icon: 'Minus', tags: ['Local'] },
];

export const DEPLOYMENT_OPTIONS: OptionItem<Deployment>[] = [
  { id: 'cloud-run', name: 'Google Cloud Run', category: 'Deployment', description: 'Serverless container deployment with auto-scaling to zero', icon: 'Cloud', popular: true, tags: ['GCP', 'Containers'] },
  { id: 'vercel', name: 'Vercel', category: 'Deployment', description: 'Instant global edge deployment platform', icon: 'Triangle', popular: true, tags: ['Edge', 'Serverless'] },
  { id: 'netlify', name: 'Netlify', category: 'Deployment', description: 'Continuous web deployment with automated previews', icon: 'Layers', tags: ['JAMstack'] },
  { id: 'aws-s3', name: 'AWS S3 + CloudFront', category: 'Deployment', description: 'Static site distribution with global AWS CDN', icon: 'Globe', tags: ['AWS', 'CDN'] },
  { id: 'github-pages', name: 'GitHub Pages', category: 'Deployment', description: 'Free hosting directly from GitHub repository builds', icon: 'Github', tags: ['Free', 'GitHub'] },
];
