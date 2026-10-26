// Verso owns elaboration, semantic HTML, hovers and source navigation.
// The existing HTML shell owns the bespoke mathematical exposition and layout.
import { readFileSync, writeFileSync, mkdirSync, readdirSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import { resolve, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseHTML } from 'linkedom';

const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
process.chdir(root);
const run = (cmd, args) => execFileSync(cmd, args, { stdio: 'inherit' });
const template = readFileSync('blueprint/page.html', 'utf8');
const { document } = parseHTML(template);
const panels = [...document.querySelectorAll('pre')];
function files(dir) {
  return readdirSync(dir, { withFileTypes: true }).flatMap(e =>
    e.isDirectory() ? files(`${dir}/${e.name}`) : e.name.endsWith('.lean') ? [`${dir}/${e.name}`] : []);
}
const sources = [...files('ElevenTwelfths'), ...files('OAI')].map(file => ({ file, text: readFileSync(file, 'utf8') }));
const escape = s => s.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
const moduleName = file => file.replace(/\.lean$/, '').replaceAll('/', '.');
const special = {
  16: ['OAI/NumberTheory/DirichletL/CubicSieve/SecondPoisson.lean', 'masked_pair_second_poisson'],
  27: ['ElevenTwelfths/SixthPowerMeanSquare.lean', 'outside_totient_moebius_bound_of_mean_square'],
};
function locate(name, panelIndex) {
  if (name === 'CanonicalDescentScale.ofReserve') return ['OAI/NumberTheory/DirichletL/CubicSieve/DescentScale.lean', 'ofReserve'];
  const matches = sources.filter(s => new RegExp(`^(?:noncomputable )?(?:def|abbrev|theorem|structure|class) ${escape(name)}(?=[\\s(:])`, 'm').test(s.text));
  if (panelIndex === 9) return ['OAI/NumberTheory/DirichletL/Arithmetic/IdealMobius.lean', name];
  const own = matches.filter(s => s.file.startsWith('ElevenTwelfths/'));
  const selected = own.length === 1 ? own[0] : matches.length === 1 ? matches[0] : null;
  if (!selected) throw Error(`Ambiguous/missing declaration ${name}: ${matches.map(s => s.file)}`);
  return [selected.file, name];
}
const plan = panels.map((p, i) => {
  const file = p.getAttribute('data-lean-source');
  if (file) return p.getAttribute('data-lean-decls').split(',').map(n => [file, n]);
  if (special[i + 1]) {
    if (!p.textContent.includes(special[i + 1][1])) throw Error(`Schematic panel ${i + 1} moved; update its explicit mapping`);
    return [special[i + 1]];
  }
  const names = [...p.textContent.matchAll(/^(?:noncomputable )?(?:def|abbrev|theorem|structure|class) ([^\s(:]+)/gm)].map(m => m[1]);
  if (!names.length) throw Error(`No declarations in panel ${i + 1}`);
  return names.map(n => locate(n, i + 1));
});
const modules = [...new Set(plan.flat().map(([file]) => moduleName(file)))];
mkdirSync('.lake/blueprint', { recursive: true });
writeFileSync('.lake/blueprint/plan.json', JSON.stringify(plan, null, 2));
if (process.argv.includes('--plan')) { console.log(modules.join('\n')); process.exit(0); }
if (!process.argv.includes('--render-only')) {
  run('node', ['scripts/sync-blueprint.mjs', '--check']);
  run('lake', ['build', ...modules.map(m => `${m}:literate`), 'verso-html']);
  run('lake', ['exe', 'verso-html', '.lake/build/literate', '_site']);
}

const rendered = new Map(modules.map(mod => {
  const html = readFileSync(`_site/${mod.replaceAll('.', '/')}/index.html`, 'utf8');
  return [mod, parseHTML(html).document];
}));
// A global declaration index gives stable links even for repeated excerpts.
const definitions = new Map();
for (const [mod, doc] of rendered) {
  for (const token of doc.querySelectorAll('.const.token[data-binding][id]')) {
    definitions.set(token.getAttribute('data-binding'), `${mod.replaceAll('.', '/')}/#${token.id}`);
  }
}
// Compiler reference metadata supplies exact modules for declarations outside
// this guide's rendered set. Never guess a declaration's namespace or file.
const references = new Map();
for (const mod of modules) {
  const data = JSON.parse(readFileSync(`.lake/build/lib/lean/${mod.replaceAll('.', '/')}.ilean`, 'utf8'));
  for (const key of Object.keys(data.references)) {
    const ref = JSON.parse(key).c;
    if (ref) references.set(`const-${ref.n}`, ref);
  }
}
const metadata = new Map();
function destination(binding) {
  if (definitions.has(binding)) return definitions.get(binding);
  const ref = references.get(binding);
  if (!ref) return null;
  if (/^(OAI|ElevenTwelfths)\./.test(ref.m)) {
    if (!metadata.has(ref.m)) metadata.set(ref.m, JSON.parse(readFileSync(`.lake/build/lib/lean/${ref.m.replaceAll('.', '/')}.ilean`, 'utf8')));
    const range = metadata.get(ref.m).decls[ref.n];
    if (!range) return null;
    return `https://github.com/AlexKontorovich/quasi-rh/blob/main/${ref.m.replaceAll('.', '/')}.lean#L${range[4]}`;
  }
  return `https://leanprover-community.github.io/mathlib4_docs/find/?pattern=${encodeURIComponent(ref.n)}#doc`;
}
for (const [mod, doc] of rendered) {
  for (const token of doc.querySelectorAll('.const.token[data-binding]')) {
    const target = destination(token.getAttribute('data-binding'));
    if (target && !token.closest('a')) {
      const a = doc.createElement('a'); a.setAttribute('href', target);
      token.replaceWith(a); a.append(token);
    }
  }
  writeFileSync(`_site/${mod.replaceAll('.', '/')}/index.html`, '<!doctype html>\n' + doc.documentElement.outerHTML);
}
// Trim the proof at the DOM-text level, retaining Verso's token/hover annotations.
function takeText(node, count) {
  for (const child of [...node.childNodes]) {
    if (count <= 0) { child.remove(); continue; }
    const size = child.textContent.length;
    if (size > count) {
      if (child.nodeType === 3) child.textContent = child.textContent.slice(0, count);
      else takeText(child, count);
    }
    count -= size;
  }
}
function textBefore(root, target) {
  let size = 0, found = false;
  function visit(node) {
    if (node === target) found = true;
    if (found) return;
    if (node.nodeType === 3) size += node.textContent.length;
    else for (const child of node.childNodes) visit(child);
  }
  visit(root);
  if (!found) throw Error('Proof delimiter not inside declaration');
  return size;
}
function excerpt(file, name, panelIndex) {
  const mod = moduleName(file), doc = rendered.get(mod);
  const candidates = [...doc.querySelectorAll('code.hl.lean.block')];
  const pattern = name === '@context' ? /^\s*variable \(m : O\)/ :
    new RegExp(`(?:^|\\n)(?:noncomputable )?(?:def|abbrev|theorem|structure|class) ${escape(name)}(?=[\\s(:])`);
  const found = candidates.filter(c => pattern.test(c.textContent));
  if (found.length !== 1) throw Error(`${mod}.${name}: expected one rendered declaration, got ${found.length}`);
  const code = found[0].cloneNode(true);
  code.setAttribute('data-lean-context', `panel-${panelIndex}-${mod}`);
  if (/^\s*theorem\b/.test(code.textContent)) {
    const delimiter = [...code.querySelectorAll('.token')].find(t =>
      t.textContent === ':=' && t.getAttribute('data-binding')?.startsWith('kw-occ-Lean.Parser.Command.declValSimple-'));
    if (!delimiter) throw Error(`Cannot find compiler-marked proof boundary: ${mod}.${name}`);
    takeText(code, textBefore(code, delimiter));
  }
  // Declarations link to complete source, not another occurrence in the guide.
  for (const a of code.querySelectorAll('a[href]')) {
    const href = a.getAttribute('href');
    if (href.startsWith('#')) a.setAttribute('href', `${mod.replaceAll('.', '/')}/${href}`);
  }
  for (const token of code.querySelectorAll('[data-binding]')) {
    const target = definitions.get(token.getAttribute('data-binding'));
    if (target && !token.closest('a')) {
      const a = document.createElement('a'); a.setAttribute('href', target);
      token.replaceWith(a); a.append(token);
    }
  }
  for (const el of [code, ...code.querySelectorAll('[id]')]) {
    if (el.id) el.id = `panel-${panelIndex}-${el.id}`;
  }
  const wrapper = document.createElement('div'); wrapper.className = 'verso-declaration';
  const link = document.createElement('a'); link.className = 'verso-source';
  const definition = found[0].querySelector('.const.token[data-binding][id]');
  link.setAttribute('href', `${mod.replaceAll('.', '/')}/${definition ? `#${definition.id}` : ''}`);
  link.textContent = `${name === '@context' ? 'Shared context' : name} · full Lean source ↗`;
  wrapper.append(link, code);
  return wrapper;
}
for (const [i, panel] of panels.entries()) {
  const box = document.createElement('div'); box.className = 'verso-code-panel';
  box.setAttribute('data-verso-panel', String(i + 1));
  for (const [file, name] of plan[i]) box.append(excerpt(file, name, i + 1));
  panel.replaceWith(box);
}
// Enrich unambiguous declaration names in prose too. Schematic formulas and
// file paths remain ordinary text rather than pretending to be checked Lean.
const inlineTokens = new Map();
for (const doc of rendered.values()) for (const token of doc.querySelectorAll('.const.token[data-verso-hover]')) {
  const name = token.textContent;
  if (!inlineTokens.has(name)) inlineTokens.set(name, new Map());
  inlineTokens.get(name).set(token.getAttribute('data-binding'), token);
}
for (const code of document.querySelectorAll('code:not(.hl)')) {
  const candidates = inlineTokens.get(code.textContent);
  if (candidates?.size !== 1) continue;
  const token = candidates.values().next().value.cloneNode(true);
  token.removeAttribute('id');
  code.classList.add('hl', 'lean', 'inline'); code.setAttribute('data-lean-context', 'prose');
  code.replaceChildren(token);
  const href = destination(token.getAttribute('data-binding'));
  if (href && !code.closest('a')) {
    const a = document.createElement('a'); a.setAttribute('href', href);
    token.replaceWith(a); a.append(token);
  }
}
// Use the exact assets emitted by the pinned Verso version, not an imitation.
const sample = rendered.values().next().value;
for (const selector of ['script:not([src])', 'style', 'script[src="popper.js"]', 'script[src="tippy.js"]', 'link[href="verso-vars.css"]', 'link[href="tippy-border.css"]']) {
  for (const element of sample.head.querySelectorAll(selector)) document.head.append(element.cloneNode(true));
}
const css = document.createElement('link'); css.rel = 'stylesheet'; css.href = 'blueprint-verso.css'; document.head.append(css);
for (const note of document.querySelectorAll('.formal-note')) {
  note.innerHTML = note.innerHTML.replace('The declarations below are synchronized directly from the Lean source; theorem proofs are omitted.',
    'Rendered from checked Lean by Verso. Hover over identifiers for types; click through to definitions and full proofs.');
}
writeFileSync('_site/blueprint-verso.css', readFileSync('blueprint/verso.css'));
writeFileSync('_site/blueprint-theme.css', readFileSync('blueprint/theme.css'));
const result = '<!doctype html>\n' + document.documentElement.outerHTML;
writeFileSync('_site/index.html', result);
writeFileSync('blueprint/index.html', result);
console.log(`Rendered ${panels.length} semantic panels from ${modules.length} Lean modules.`);
