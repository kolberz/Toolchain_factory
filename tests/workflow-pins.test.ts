import assert from 'node:assert/strict';
import { readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import test from 'node:test';

const repositoryRoot = path.resolve(import.meta.dirname, '..');

test('every remote GitHub Action is pinned to an immutable commit SHA', () => {
  const workflowDirectory = path.join(repositoryRoot, '.github', 'workflows');
  for (const name of readdirSync(workflowDirectory).filter(candidate => /\.ya?ml$/.test(candidate))) {
    const contents = readFileSync(path.join(workflowDirectory, name), 'utf8');
    for (const match of contents.matchAll(/\buses:\s+([^./\s][^@\s]*)@([^\s#]+)/g)) {
      assert.match(match[2], /^[0-9a-f]{40}$/, `${name}: ${match[1]} uses mutable ref ${match[2]}`);
    }
  }
});

test('the offline verifier base image is pinned by registry digest', () => {
  const dockerfile = readFileSync(path.join(repositoryRoot, 'scripts', 'offline-verifier.Dockerfile'), 'utf8');
  assert.match(dockerfile, /^FROM\s+ubuntu:24\.04@sha256:[0-9a-f]{64}\s*$/m);
});

test('the Zeta verifier fetches nanoda from the repository containing the pinned tree', () => {
  const workflow = readFileSync(
    path.join(repositoryRoot, '.github', 'workflows', 'verify-zeta23.yml'),
    'utf8',
  );
  assert.match(workflow, /git clone https:\/\/github\.com\/ammkrn\/nanoda_lib\.git zeta-tools\/nanoda/);
  assert.doesNotMatch(workflow, /github\.com\/robsimmons\/nanoda_lib/);
});
