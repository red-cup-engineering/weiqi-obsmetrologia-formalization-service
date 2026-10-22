import assert from 'node:assert/strict';
import { test } from 'node:test';
import { mkdtempSync, mkdirSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { inspectProofWorkspace, runProofTarget } from '../scripts/proof-preflight.mjs';

function fixture(testFn) {
  const root = mkdtempSync(join(tmpdir(), 'weiqi-proof-'));
  try {
    const lake = join(root, 'lib', 'weiqi-obsmetrologia');
    mkdirSync(join(lake, 'WeiqiObsmetrologia'), { recursive: true });
    writeFileSync(join(lake, 'lean-toolchain'), 'leanprover/lean4:v4.31.0\n');
    writeFileSync(join(lake, 'WeiqiObsmetrologia', 'ReachClosure.lean'), '-- proof candidate\n');
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
}));

test('unknown module target is refused before any execution', () => fixture(root => {
  const read = runProofTarget(root, 'invented');
  assert.equal(read.status, 'refused');
  assert.equal(read.reason, 'unknown-target');
}));
