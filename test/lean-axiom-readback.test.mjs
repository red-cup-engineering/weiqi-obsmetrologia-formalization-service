import assert from 'node:assert/strict';
import { test } from 'node:test';
import { declaredAxiomProbes, auditAxiomReadback, PROOF_MODULES,
  ALLOWED_AXIOMS } from '../scripts/lean-axiom-readback.mjs';

const names=[
  'WeiqiObsmetrologia.Board.reachClosure_closed',
  'WeiqiObsmetrologia.Ko.positionalSuperko_length_le',
];
const clean=[
  "'WeiqiObsmetrologia.Board.reachClosure_closed' does not depend on any axioms",
  "'WeiqiObsmetrologia.Ko.positionalSuperko_length_le' depends on axioms: [Quot.sound]",
].join('\n');

test('accepts only complete transitive kernel axiom readback under the original policy',()=>{
  const r=auditAxiomReadback(clean,names);
  assert.equal(r.status,'kernel-axiom-policy-passed');
  assert.equal(r.expected,2);
  assert.equal(r.received,2);
  assert.deepEqual(r.forbidden,[]);
  assert.deepEqual(ALLOWED_AXIOMS,['Quot.sound']);
  assert.equal(PROOF_MODULES.length,5);
});

test('forbidden imported propext, Classical.choice, and sorryAx each refuse',()=>{
  for (const axiom of ['propext','Classical.choice','sorryAx','NewAxiom']) {
    const source=clean.replace('[Quot.sound]','[Quot.sound, '+axiom+']');
    const r=auditAxiomReadback(source,names);
    assert.equal(r.status,'refused-axiom-evidence');
    assert.deepEqual(r.forbidden,[{declaration:names[1],axiom}]);
  }
});

test('no compiler readback is never a false positive',()=>{
  const r=auditAxiomReadback('Build completed successfully\n',names);
  assert.equal(r.received,0);
  assert.deepEqual(r.missing,names);
  assert.equal(r.status,'refused-axiom-evidence');
});

test('truncated, duplicated, unrelated and poisoned readbacks refuse',()=>{
  const truncated=auditAxiomReadback(clean.split('\n')[0],names);
  assert.deepEqual(truncated.missing,[names[1]]);
  const dup=auditAxiomReadback(clean+'\n'+clean.split('\n')[0],names);
  assert.deepEqual(dup.duplicates,[names[0]]);
  const foreign=auditAxiomReadback(clean+"\n'External.random' does not depend on any axioms",names);
  assert.deepEqual(foreign.unknown,['External.random']);
  for(const r of [truncated,dup,foreign])
    assert.equal(r.status,'refused-axiom-evidence');
});

test('collects unique probes from all five ORIGINAL Weiqi Lean sources',()=>{
  const source=PROOF_MODULES.map((name,i)=>
    '#print axioms WeiqiObsmetrologia.'+name+'.theorem_'+i+'\n');
  const probes=declaredAxiomProbes(source);
  assert.equal(probes.length,5);
  assert.ok(Object.isFrozen(probes));
  const subset=declaredAxiomProbes([source[4]],['ReachClosure']);
  assert.deepEqual(subset,['WeiqiObsmetrologia.ReachClosure.theorem_4']);
  assert.throws(()=>declaredAxiomProbes([],[]),/nonempty/);
  assert.throws(()=>declaredAxiomProbes(['#print axioms Foo.test'],['ReachClosure']),/no axiom probes/);
  assert.throws(()=>declaredAxiomProbes([source[0],source[0]],['Board','Ko']),/duplicate original/);
  assert.throws(()=>declaredAxiomProbes([source[0]],['Unknown']),/original modules/);
});

test('rejects duplicate expected names and text that is not a kernel axiom report',()=>{
  assert.throws(()=>auditAxiomReadback(clean,[names[0],names[0]]),/unique original names/);
  assert.throws(()=>auditAxiomReadback(null,names),/requires output/);
  const ignored=auditAxiomReadback('some stdout quote: [Quot.sound]',names);
  assert.equal(ignored.status,'refused-axiom-evidence');
  assert.equal(ignored.received,0);
});
