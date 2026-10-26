import assert from 'node:assert/strict';
import { readFileSync, existsSync } from 'node:fs';
import { parseHTML } from 'linkedom';

const { document } = parseHTML(readFileSync('_site/index.html', 'utf8'));
const { document: template } = parseHTML(readFileSync('blueprint/page.html', 'utf8'));
const panels = [...document.querySelectorAll('[data-verso-panel]')];
assert.equal(panels.length, template.querySelectorAll('pre').length);
assert.equal(document.querySelectorAll('pre').length, 0, 'No inert legacy code panels');
for (const panel of panels) {
  assert.ok(panel.querySelector('code.hl.lean.block'), 'Panel uses Verso rendering');
  assert.ok(panel.querySelector('[data-verso-hover]'), 'Panel contains semantic hovers');
  assert.ok(panel.querySelector('a.verso-source'), 'Panel links to complete source');
}
const hovers = JSON.parse(readFileSync('_site/-verso-docs.json', 'utf8'));
assert.ok(Object.keys(hovers).length > 0, 'Nonempty compiler-generated hover table');
for (const token of document.querySelectorAll('[data-verso-hover]')) {
  assert.ok(Object.hasOwn(hovers, token.getAttribute('data-verso-hover')), 'Every hover id resolves');
}
const ids = [...document.querySelectorAll('[id]')].map(el => el.id);
assert.equal(new Set(ids).size, ids.length, 'Unique HTML ids, including repeated declarations');
const targetDocuments = new Map();
for (const a of document.querySelectorAll('.verso-code-panel a[href]')) {
  const href = a.getAttribute('href');
  if (/^(https?:|#)/.test(href)) continue;
  const [path, fragment] = href.split('#');
  const file = `_site/${path}${path.endsWith('/') ? 'index.html' : ''}`;
  assert.ok(existsSync(file), `Missing link destination ${href}`);
  if (fragment) {
    if (!targetDocuments.has(file)) targetDocuments.set(file, parseHTML(readFileSync(file, 'utf8')).document);
    const target = targetDocuments.get(file);
    assert.ok(target.getElementById(decodeURIComponent(fragment)), `Missing anchor ${href}`);
  }
}
for (const section of template.querySelectorAll('section[id]')) {
  assert.ok(document.getElementById(section.id), `Preserve section ${section.id}`);
}
assert.equal(document.querySelector('h1').textContent, template.querySelector('h1').textContent);
assert.deepEqual([...document.querySelectorAll('.story')].map(el => el.textContent),
  [...template.querySelectorAll('.story')].map(el => el.textContent), 'Mathematical exposition is unchanged');
console.log(`Validated ${panels.length} Verso panels, hover data, unique ids and source links.`);
