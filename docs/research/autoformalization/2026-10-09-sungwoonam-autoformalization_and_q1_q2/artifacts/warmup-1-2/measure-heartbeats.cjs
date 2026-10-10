// Usage: node measure-heartbeats.cjs <Strata checkout> [absolute lake executable] [output directory]
// Each proof is freshly elaborated in its own Lean process, under the same name.
// Requires a built Strata.Transform.CallElimCorrect at the pinned revision/toolchain.
const fs = require('node:fs');
const path = require('node:path');
const {spawnSync} = require('node:child_process');
const assert = require('node:assert/strict');
const strata = path.resolve(process.argv[2] || '.');
const lake = process.argv[3] || 'lake';
const output = path.resolve(process.argv[4] || path.join(strata, 'warmup-heartbeats'));
fs.mkdirSync(output, {recursive: true});
function run(executable, args, cwd = strata) {
  const r = spawnSync(executable, args, {cwd, encoding: 'utf8', timeout: 120000});
  const log = (r.stdout || '') + (r.stderr || '');
  assert.equal(r.status, 0, r.error?.message || log);
  return log;
}
const revision = run('git', ['rev-parse', 'HEAD']).trim();
assert.equal(revision, '451e5f047bafa010d178856db76c00029bfa4d7f');
assert.equal(fs.readFileSync(path.join(strata, 'lean-toolchain'),'utf8').trim(), 'leanprover/lean4:v4.26.0');
const leanVersion = run(lake, ['env', 'lean', '--version']).trim();
assert(leanVersion.includes('version 4.26.0'));
const originalFile = fs.readFileSync(path.join(__dirname, 'verify_warmup_1_2.lean'),'utf8');
const improvedFile = fs.readFileSync(path.join(__dirname, 'improved_proofs.lean'),'utf8');
const names = ['substOldPostSubset', 'extractedOldExprInVars'];
const original = names.map(name => {
  const m = originalFile.match(new RegExp('theorem original_' + name + '([\\s\\S]*?) := by\\r?\\n([\\s\\S]*?)(?=#print)'));
  assert(m);
  return {statement: 'theorem target' + m[1], body: m[2].trimEnd()};
});
const improved = names.map(name => {
  const m = improvedFile.match(new RegExp('theorem improved_' + name + '([\\s\\S]*?) := by\\r?\\n([\\s\\S]*?)(?=\\n\\n(?:open |#print))'));
  assert(m);
  const reference = original[names.indexOf(name)].statement;
  assert.equal(('theorem target' + m[1]).replace(/\s/g,''), reference.replace(/\s/g,''));
  return m[2].trimEnd();
});
const additions = fs.readFileSync(path.join(__dirname,'CallElimCorrect.patch'),'utf8').split(/\r?\n/)
  .filter(s => s.startsWith('+') && !s.startsWith('+++')).map(s => s.slice(1));
const boundary = additions.findIndex(s => s.includes('induction post'));
assert(boundary > 0);
const proofs = {
  original: original.map(p => p.body),
  previous: [additions.slice(boundary).join('\n'), additions.slice(0,boundary).join('\n')],
  improved
};
const prefix = `import Lean
import Strata.Transform.CallElimCorrect
set_option Elab.async false
open Lean Elab Command
elab "#measure " c:command : command => do
  let (_, ticks) ← withHeartbeats (elabCommand c)
  logInfo m!"RAW_HEARTBEATS={ticks}"
namespace WarmupMeasure
open Core Core.Transform CallElim OldExpressions CallElimCorrect
`;
const results = {
  measured_on: new Intl.DateTimeFormat('en-CA', {timeZone: 'Asia/Seoul'}).format(new Date()), revision, lean_version: leanVersion,
  checkout_changes: run('git', ['status', '--short']),
  method: 'Lean.withHeartbeats around synchronous elabCommand; Elab.async=false; imports excluded; includes declaration elaboration/checking; separate process and identical declaration name per proof; raw counter divided by 1000',
  official_arena_harness: false,
  repetitions: 3, results: []
};
for (const [variant, bodies] of Object.entries(proofs)) {
  for (let problem = 0; problem < 2; problem++) {
    const body = bodies[problem];
    const source = prefix + '#measure\n' + original[problem].statement + ' := by\n' + body + '\n#print axioms target\nend WarmupMeasure\n';
    const stem = variant + '-' + (problem + 1);
    const file = path.join(output, stem + '.lean');
    fs.writeFileSync(file, source);
    const raw = [];
    for (let i = 0; i < results.repetitions; i++) {
      const log = run(lake, ['env', 'lean', file]);
      fs.writeFileSync(path.join(output, stem + '-run' + (i+1) + '.log'), log);
      assert(!/sorryAx|error:|error\(/.test(log), log);
      assert(log.includes("'WarmupMeasure.target' depends on axioms: [propext, Quot.sound]"), log);
      const matches = [...log.matchAll(/RAW_HEARTBEATS=(\d+)/g)];
      assert.equal(matches.length, 1);
      raw.push(Number(matches[0][1]));
    }
    const medianRaw = [...raw].sort((a,b) => a-b)[1];
    const item = {
      problem: problem + 1, declaration: names[problem], variant,
      raw_heartbeats: raw, median_heartbeats: medianRaw / 1000,
      nonempty_body_lines: body.split(/\r?\n/).filter(s => s.trim()).length,
      characters_without_whitespace: body.replace(/\s/g,'').length,
      axioms: ['propext', 'Quot.sound'], exit_codes: [0,0,0]
    };
    results.results.push(item);
    console.log(JSON.stringify(item));
  }
}
fs.writeFileSync(path.join(output, 'measurements.json'), JSON.stringify(results,null,2) + '\n');
console.log('All proofs verified; measurements saved to ' + output);
