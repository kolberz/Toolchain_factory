import { DefaultArtifactClient } from '@actions/artifact';
import { readdir, writeFile } from 'node:fs/promises';
import path from 'node:path';

const [partsArgument, outputArgument] = process.argv.slice(2);
if (!partsArgument || !outputArgument) {
  console.error('usage: node scripts/upload-artifact-parts.mjs PARTS_DIRECTORY OUTPUT_JSON');
  process.exit(64);
}

const partsDirectory = path.resolve(partsArgument);
const outputPath = path.resolve(outputArgument);
const filenames = (await readdir(partsDirectory))
  .filter(filename => /^portable-lean-toolchain\.tar\.zst\.part-[0-9]{3,}$/.test(filename))
  .sort();

if (filenames.length === 0) throw new Error(`No archive parts found in ${partsDirectory}`);
if (filenames.length > 498) throw new Error(`Part count ${filenames.length} exceeds the per-job artifact budget.`);

const artifact = new DefaultArtifactClient();
const uploaded = [];
const connectorWrapperLimit = 512 * 1024 * 1024;
for (const filename of filenames) {
  const suffix = filename.slice(filename.lastIndexOf('-') + 1);
  const name = `portable-lean-toolchain-part-${suffix}`;
  const response = await artifact.uploadArtifact(
    name,
    [path.join(partsDirectory, filename)],
    partsDirectory,
    { compressionLevel: 0, retentionDays: 90 }
  );
  if (!response.id || !response.digest || !response.size) throw new Error(`Artifact upload did not return complete metadata for ${name}`);
  if (response.size >= connectorWrapperLimit) throw new Error(`${name} wrapper is not below 512 MiB: ${response.size} bytes`);
  uploaded.push({ name, filename, id: response.id, digest: response.digest, wrapperBytes: response.size });
  console.log(`uploaded ${name}: id=${response.id} bytes=${response.size} digest=${response.digest}`);
}

await writeFile(outputPath, `${JSON.stringify({ schemaVersion: '1.0.0', uploaded }, null, 2)}\n`);
