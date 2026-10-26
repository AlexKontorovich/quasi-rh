import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';

const html = readFileSync(new URL('../blueprint/page.html', import.meta.url), 'utf8');
let panels = 0;
for (const match of html.matchAll(
  /<pre data-lean-source="[^"]+" data-lean-decls="([^"]+)"><code>([\s\S]*?)<\/code><\/pre>/g)) {
  const expected = match[1].split(',').filter(name => name !== '@context');
  const actual = [...match[2].matchAll(/^(?:noncomputable )?(?:def|abbrev|theorem) ([^\s(]+)/gm)]
    .map(declaration => declaration[1]);
  assert.deepEqual(actual, expected, 'Each requested declaration should appear exactly once, in order');
  panels++;
}
assert.ok(panels > 0, 'Expected source-synchronized panels');
console.log(`${panels} panels contain exactly their requested declarations.`);
