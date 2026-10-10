// Checks presentation fidelity to the compiled improved proofs; does not invoke Lean.
const fs = require('node:fs');
const path = require('node:path');
const assert = require('node:assert/strict');
const vm = require('node:vm');
const pagePath = path.resolve(__dirname, '../../warmup-problems-1-2.html');
const html = fs.readFileSync(pagePath, 'utf8');
const original = fs.readFileSync(path.join(__dirname, 'verify_warmup_1_2.lean'), 'utf8');
const improved = fs.readFileSync(path.join(__dirname, 'improved_proofs.lean'), 'utf8');
const measured = JSON.parse(fs.readFileSync(path.join(__dirname, 'heartbeat-2026-10-10/measurements.json'), 'utf8'));
const evidence = JSON.parse(fs.readFileSync(path.join(__dirname, 'warmup_1_2_verification.json'), 'utf8'));
const decode = s => s.replace(/&lt;/g, '<').replace(/&gt;/g, '>').replace(/&amp;/g, '&');
const compact = s => s.replace(/--[^\r\n]*/g, '').replace(/\s/g, '');
const metrics = s => ({
  nonempty_body_lines: s.split(/\r?\n/).filter(line => line.trim()).length,
  characters_without_whitespace: s.replace(/\s/g, '').length
});
const candidates = ['substOldPostSubset', 'extractedOldExprInVars'].map(name => {
  const match = improved.match(new RegExp('theorem improved_' + name + '[\\s\\S]*? := by\\r?\\n([\\s\\S]*?)(?=\\n\\n(?:open |#print))'));
  assert(match, name);
  return match[1];
});
const displayed = [...html.matchAll(/<div class="code-block after">[\s\S]*?<pre class="lean"><code>([\s\S]*?)<\/code>/g)].map(m => decode(m[1]));
assert.equal(displayed.length, 2);
const names = ['substOldPostSubset', 'extractedOldExprInVars'];
for (const [i, name] of names.entries()) {
  const declaration = original.match(new RegExp('theorem original_' + name + '([\\s\\S]*?) := by\\r?\\n([\\s\\S]*?)(?=#print)'));
  assert(declaration, name);
  assert.deepEqual(metrics(declaration[2]), evidence.problems[i].original, name + ': original size');
  const measurement = measured.results.find(r => r.problem === i+1 && r.variant === 'improved');
  assert.deepEqual(metrics(candidates[i]), {nonempty_body_lines: measurement.nonempty_body_lines, characters_without_whitespace: measurement.characters_without_whitespace}, name + ': candidate size');
  assert.equal(compact(displayed[i]), compact(candidates[i]), name + ': proof text');
  const statement = html.match(new RegExp('theorem ' + name + '([\\s\\S]*?)<\\/code>'));
  assert(statement, name + ': displayed statement');
  assert.equal(compact(decode(statement[1])), compact(declaration[1]), name + ': statement');
  console.log(name, JSON.stringify({original: metrics(declaration[2]), candidate: metrics(candidates[i]), proof_text: 'identical except comments/whitespace', statement: 'identical'}));
}
const ids = [...html.matchAll(/\bid="([^"]+)"/g)].map(m => m[1]);
assert(html.trimEnd().endsWith('</html>'), 'complete HTML document');
assert.equal(new Set(ids).size, ids.length, 'unique HTML IDs');
for (const [, href] of html.matchAll(/\bhref="([^"]+)"/g)) {
  if (href.startsWith('#')) assert(ids.includes(href.slice(1)), 'anchor ' + href);
  else if (!/^[a-z]+:/i.test(href)) assert(fs.existsSync(path.resolve(path.dirname(pagePath), href.split('#')[0])), 'file ' + href);
}
// Run the actual demo script with a minimal DOM to check its bounded state flow.
const elements = new Map();
function element() {
  return {textContent: '', disabled: false, listeners: {}, classes: new Set(),
    addEventListener(type, fn) { this.listeners[type] = fn; },
    classList: {toggle() {}}};
}
for (const id of ['ast-next', 'ast-reset', 'ast-status']) elements.set(id, element());
const nodes = Array.from({length: 6}, () => {
  const el = element();
  el.classList.toggle = (name, value) => value ? el.classes.add(name) : el.classes.delete(name);
  return el;
});
const script = [...html.matchAll(/<script>([\s\S]*?)<\/script>/g)].map(m => m[1]).join('\n');
vm.runInNewContext(script, {document: {
  getElementById: id => elements.get(id),
  querySelectorAll: selector => selector === '[data-node]' ? nodes : []
}});
assert.match(elements.get('ast-status').textContent, /모은 이름: \[\]/);
const expected = ['[]', '[x]', '[x]', '[x]', '[x, y]', '[x, y, z]'];
expected.forEach((suffix, i) => {
  elements.get('ast-next').listeners.click();
  assert(elements.get('ast-status').textContent.endsWith(suffix));
  assert(nodes[i].classes.has('active'));
  assert.equal(nodes.filter(n => n.classes.has('active')).length, 1);
});
assert.equal(elements.get('ast-next').disabled, true);
elements.get('ast-reset').listeners.click();
assert.equal(elements.get('ast-next').disabled, false);
assert(nodes.every(n => n.classes.size === 0));
assert.match(elements.get('ast-status').textContent, /방문 전/);
console.log('HTML links, proof fidelity, and traversal/reset checks passed. Lean compilation and heartbeat results are recorded separately.');
