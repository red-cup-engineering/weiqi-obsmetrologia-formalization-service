import assert from 'node:assert/strict';
import { test } from 'node:test';
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { inspectProofWorkspace, runProofTarget, lexicallyAuditLeanSource } from '../scripts/proof-preflight.mjs';

function fixture(testFn) {
  const root = mkdtempSync(join(tmpdir(), 'weiqi-proof-'));
  try {
    const lake = join(root, 'lib', 'weiqi-obsmetrologia');
    mkdirSync(join(lake, 'WeiqiObsmetrologia'), { recursive: true });
    writeFileSync(join(lake, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    for (const name of ['Board','Ko','Evidence','Admission','ReachClosure'])
      writeFileSync(join(lake,'WeiqiObsmetrologia',name+'.lean'),'-- proof candidate\n');
    writeFileSync(join(lake, 'lakefile.toml'), [
      'name = "WeiqiObsmetrologia"',
      '[[require]]', 'name = "Obsmetrologia"', 'path = "../../source-obs"',
      '[[require]]', 'name = "ObsmetrologiaComputing"', 'path = "../../source-computing"',
    ].join('\n'));
    testFn(root, lake);
  } finally { rmSync(root, { recursive: true, force: true }); }
}

test('missing source mounts block native proof and never produce a pass', () => fixture(root => {
  const read = inspectProofWorkspace(root);
  assert.equal(read.status, 'blocked');
  assert.deepEqual(read.errors, ['unmounted:Obsmetrologia', 'unmounted:ObsmetrologiaComputing']);
  assert.equal(runProofTarget(root, 'reach').attemptedBuild, false);
  assert.equal(read.toolchain, 'leanprover/lean4:v4.31.0');
}));

test('original declared source layout is inspected without changing lakefile', () => fixture((root, lake) => {
  for (const name of ['source-obs', 'source-computing']) {
    mkdirSync(join(root, name), { recursive: true });
    writeFileSync(join(root, name, 'lakefile.toml'), 'name = "source"\n');
    writeFileSync(join(root, name,
      name === 'source-obs' ? 'Obsmetrologia.lean' : 'ObsmetrologiaComputing.lean'), '-- source\n');
  }
  const read = inspectProofWorkspace(root);
  assert.equal(read.status, 'source-mounts-present');
  assert.equal(read.errors.length, 0);
  assert.equal(read.dependencies.every(x => x.sourcePresent), true);
  assert.equal(typeof read.reachSourceSha256, 'string');
  assert.deepEqual(Object.keys(read.sourceModuleSha256),
    ['Board','Ko','Evidence','Admission','ReachClosure']);
  assert.equal(Object.values(read.sourceModuleSha256).every(v=>typeof v==='string'),true);
  assert.equal(read.dependencies.every(x=>typeof x.dependencyManifestSha256==='string'),true);
}));

test('unknown module target is refused before any execution', () => fixture(root => {
  const read = runProofTarget(root, 'invented');
  assert.equal(read.status, 'refused');
  assert.equal(read.reason, 'unknown-target');
}));


test('local Lean axiom-law violations refuse builds before opening Lake', () => fixture((root,lake) => {
  const file = join(lake,'WeiqiObsmetrologia','ReachClosure.lean');
  writeFileSync(file,[
    '/-! A word propext in a nested documentation comment is not source debt.',
    '    /- sorry is not code either -/',
    '-/',
    'theorem illegal : True := by',
    '  have h := propext',
  ].join('\n'));
  const read=inspectProofWorkspace(root);
  assert.ok(read.errors.includes('local-axiom-law:propext'));
  assert.equal(read.localProofAudit.status,'refuse-lexically');
  assert.equal(runProofTarget(root,'reach').attemptedBuild,false);
  writeFileSync(file, 'axiom Unlicensed : Prop\n');
  assert.ok(inspectProofWorkspace(root).errors.includes('local-axiom-law:new-axiom-declaration'));
}));

test('nested comments are ignored but unfinished comments refuse', () => {
  const okay=lexicallyAuditLeanSource('/- sorry /- propext -/ -/ theorem t : True := by exact True.intro');
  assert.equal(okay.status,'no-local-lexical-obstruction');
  const bad=lexicallyAuditLeanSource('/- unfinished block');
  assert.deepEqual(bad.forbiddenTokens,['unterminated-lean-comment']);
  const sorry=lexicallyAuditLeanSource('theorem t : True := by sorry');
  assert.deepEqual(sorry.forbiddenTokens,['sorry']);
  assert.equal(okay.qualification,'not-a-kernel-or-imported-axiom-check');
});

test('mismatched declared Lean toolchain refuses before invoking Lake', () => fixture((root,lake) => {
  for (const name of ['source-obs','source-computing']) {
    const at=join(root,name);
    mkdirSync(at,{recursive:true});
    writeFileSync(join(at,'lakefile.toml'),'name = "source"\n');
    writeFileSync(join(at,name==='source-obs'?'Obsmetrologia.lean':'ObsmetrologiaComputing.lean'),'-- source\n');
    writeFileSync(join(at,'lean-toolchain'),name==='source-obs'
      ? 'leanprover/lean4:v4.32.0\n' : 'leanprover/lean4:v4.31.0\n');
  }
  const read=inspectProofWorkspace(root);
  assert.deepEqual(read.errors,['toolchain-mismatch:Obsmetrologia']);
  assert.equal(runProofTarget(root,'reach').attemptedBuild,false);
}));


test('all local theorem declarations require real axiom probes, not docstring ghosts', () => {
  const annotated = [
    '/-! theorem phantom never exists: it is only documentation -/',
    'theorem real : True := by exact True.intro',
    '#print axioms WeiqiObsmetrologia.Board.real',
  ].join('\n');
  const okay=lexicallyAuditLeanSource(annotated,{requireProbes:true});
  assert.deepEqual(okay.forbiddenTokens,[]);
  assert.equal(okay.localTheoremCount,1);
  assert.equal(okay.localAxiomProbeCount,1);
  const bad=lexicallyAuditLeanSource(
    annotated + '\n#print axioms WeiqiObsmetrologia.Board.phantom',
    {requireProbes:true});
  assert.ok(bad.forbiddenTokens.includes('unknown-local-axiom-probe:phantom'));
  const absent=lexicallyAuditLeanSource('theorem missing : True := by exact True.intro',
    {requireProbes:true});
  assert.ok(absent.forbiddenTokens.includes('missing-local-axiom-probe:missing'));
});


test('missing any local proof module blocks before Lake and identifies that source',()=>fixture((root,lake)=>{
  rmSync(join(lake,'WeiqiObsmetrologia','Evidence.lean'));
  const result=inspectProofWorkspace(root);
  assert.ok(result.errors.includes('missing-local-proof-module:Evidence'));
  assert.equal(result.sourceModuleSha256.Evidence,null);
  assert.equal(runProofTarget(root,'all').attemptedBuild,false);
}));
