// Keep marked blueprint panels verbatim synchronized with checked Lean source.
// Usage: node scripts/sync-blueprint.mjs [--check]
import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, resolve } from 'node:path';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const htmlPath = resolve(root, 'blueprint/index.html');
const before = readFileSync(htmlPath, 'utf8');
const escapeHtml = text => text.replaceAll('&', '&amp;')
  .replaceAll('<', '&lt;').replaceAll('>', '&gt;');

function declaration(file, name) {
  const source = readFileSync(resolve(root, file), 'utf8');
  if (name === '@context') {
    const context = /^variable [\s\S]*?(?=\n\n)/m.exec(source);
    if (!context) throw new Error('Shared variables not found: ' + file);
    return context[0];
  }
  const escaped = name.replace(/[.*+?^$()|[\]\\]/g, '\\$&');
  const start = new RegExp('^(?:noncomputable )?(def|abbrev|theorem) ' +
    escaped + '(?=\\s|\\()', 'm').exec(source);
  if (!start) throw new Error('Declaration not found: ' + file + '#' + name);
  const rest = source.slice(start.index);
  const next = rest.indexOf('\n\n');
  let text = (next < 0 ? rest : rest.slice(0, next)).trimEnd();
  if (start[1] === 'theorem') {
    const proof = text.indexOf(' :=');
    if (proof < 0) throw new Error('Proof boundary not found: ' + name);
    text = text.slice(0, proof);
  }
  return text;
}

let count = 0;
const after = before.replace(
  /<pre data-lean-source="([^"]+)" data-lean-decls="([^"]+)"><code>[\s\S]*?<\/code><\/pre>/g,
  (_, file, names) => {
    count++;
    const code = names.split(',').map(name => declaration(file, name)).join('\n\n');
    return '<pre data-lean-source="' + file + '" data-lean-decls="' + names +
      '"><code>' + escapeHtml(code) + '</code></pre>';
  });
if (!count) throw new Error('No source-synchronized panels found');
if (process.argv.includes('--check')) {
  if (before !== after) {
    console.error('Blueprint excerpts are stale; run node scripts/sync-blueprint.mjs');
    process.exitCode = 1;
  } else console.log(count + ' Lean panels match their source declarations.');
} else {
  writeFileSync(htmlPath, after);
  console.log('Synchronized ' + count + ' Lean panels.');
}
