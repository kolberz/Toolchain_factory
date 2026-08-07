import JSZip from 'jszip';
import { GeneratedFile } from '../types/toolchain';

export async function downloadProjectZip(projectName: string, files: GeneratedFile[]): Promise<void> {
  const zip = new JSZip();

  // Add every generated file to zip structure
  files.forEach((f) => {
    zip.file(f.path, f.content);
  });

  // Generate zip file blob
  const blob = await zip.generateAsync({ type: 'blob' });

  // Trigger client download
  const url = URL.createObjectURL(blob);
  const a = document.createElement('a');
  a.href = url;
  a.download = `${projectName.toLowerCase().replace(/[^a-z0-9-_]/g, '-')}-toolchain.zip`;
  document.body.appendChild(a);
  a.click();
  document.body.removeChild(a);
  URL.revokeObjectURL(url);
}
