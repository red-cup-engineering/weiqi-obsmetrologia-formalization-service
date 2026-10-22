import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runNativeAxiomAudit } from './lean-axiom-readback.mjs';

const MODULES = Object.freeze({
  all: null,
  board: 'WeiqiObsmetrologia.Board',
  reach: 'WeiqiObsmetrologia.ReachClosure',
  ko: 'WeiqiObsmetrologia.Ko',
  evidence: 'WeiqiObsmetrologia.Evidence',
  admission: 'WeiqiObsmetrologia.Admission',
});
const REQUIRED = Object.freeze({
  Obsmetrologia: 'Obsmetrologia.lean',
  ObsmetrologiaComputing: 'ObsmetrologiaComputing.lean',
});

function digest(path) {
  return existsSync(path)
    ? createHash('sha256').update(readFileSync(path)).digest('hex') : null;
}

/**
 * A cheap, source-local *negative gate*: strip nested Lean block/line comments
 * and refuse textual uses of axiom creation, propext, sorry or admit.
 * This is not the Lean kernel and cannot inspect imported proof dependencies.
 * Its purpose is to reject obvious illegal proof debt BEFORE expensive Lake.
 */
export function lexicallyAuditLeanSource(source, { requireProbes = false } = {}) {
  if (typeof source !== 'string') throw new TypeError('Lean source must be text');
  let code = '', depth = 0, line = false;
  for (let i=0; i<source.length;) {
    if (line) {
      if (source[i] === '\n') { line=false; code+='\n'; }
      i++; continue;
    }
    if (depth>0) {
      if (source.startsWith('/-', i)) { depth++; i+=2; }
      else if (source.startsWith('-/', i)) { depth--; i+=2; }
      else { if (source[i]==='\n') code+='\n'; i++; }
      continue;
    }
    if (source.startsWith('/-',i)) { depth++; i+=2; continue; }
    if (source.startsWith('--',i)) { line=true; i+=2; continue; }
    code+=source[i++];
  }
  const tokens = new Set();
  for (const token of ['propext','sorry','admit']) {
    if (new RegExp('\\b'+token+'\\b','u').test(code)) tokens.add(token);
  }
  if (/^\s*(?:axiom|constant)\b/mu.test(code)) tokens.add('new-axiom-declaration');
  if (depth!==0) tokens.add('unterminated-lean-comment');
  const theoremNames = [...code.matchAll(/^\s*theorem\s+([A-Za-z][A-Za-z0-9_']*)/gmu)]
    .map(match=>match[1]);
  const axiomProbeNames = [...code.matchAll(/^\s*#print\s+axioms\s+WeiqiObsmetrologia\.Board\.([A-Za-z][A-Za-z0-9_']*)/gmu)]
    .map(match=>match[1]);
  if (requireProbes) {
    for (const n of theoremNames)
      if (!axiomProbeNames.includes(n)) tokens.add('missing-local-axiom-probe:' + n);
    for (const n of axiomProbeNames)
      if (!theoremNames.includes(n)) tokens.add('unknown-local-axiom-probe:' + n);
  }
  return Object.freeze({
    kind:'weiqi.localLeanLexicalGate.v1',
    status:tokens.size?'refuse-lexically':'no-local-lexical-obstruction',
    forbiddenTokens:Object.freeze([...tokens]),
    localTheoremCount:theoremNames.length,
    localAxiomProbeCount:axiomProbeNames.length,
    qualification:'not-a-kernel-or-imported-axiom-check',
  });
}

/** Inspect actual file mounts, not promises, package names, or cached prose. */
export function inspectProofWorkspace(root) {
  const lakeDir = join(resolve(root), 'lib', 'weiqi-obsmetrologia');
  const config = join(lakeDir, 'lakefile.toml');
  const toolchainFile = join(lakeDir, 'lean-toolchain');
  const errors = [];
  if (!existsSync(config)) errors.push('missing-lakefile');
  if (!existsSync(toolchainFile)) errors.push('missing-lean-toolchain');
  const toml = existsSync(config) ? readFileSync(config, 'utf8') : '';
  const declared = new Map();
  for (const block of toml.split('[[require]]').slice(1)) {
    const name = block.match(/^\s*name\s*=\s*"([^"]+)"/m)?.[1];
    const path = block.match(/^\s*path\s*=\s*"([^"]+)"/m)?.[1];
    if (name && path) declared.set(name, path);
  }
  const dependencies = Object.entries(REQUIRED).map(([name,entrypoint]) => {
    const declaredPath = declared.get(name) ?? null;
    const absolutePath = declaredPath ? resolve(lakeDir, declaredPath) : null;
    const sourcePresent = absolutePath !== null &&
      existsSync(join(absolutePath, entrypoint)) &&
      existsSync(join(absolutePath, 'lakefile.toml'));
    if (!declaredPath) errors.push('undeclared:' + name);
    else if (!sourcePresent) errors.push('unmounted:' + name);
    return { name, declaredPath, absolutePath, sourcePresent,
      dependencyToolchain:sourcePresent && existsSync(join(absolutePath,'lean-toolchain'))
        ? readFileSync(join(absolutePath,'lean-toolchain'),'utf8').trim() : null,
    };
  });
  const toolchain = existsSync(toolchainFile)
    ? readFileSync(toolchainFile, 'utf8').trim() : null;
  for (const dep of dependencies)
    if (dep.dependencyToolchain && toolchain && dep.dependencyToolchain !== toolchain)
      errors.push('toolchain-mismatch:' + dep.name);
  const reachSource=join(lakeDir, 'WeiqiObsmetrologia', 'ReachClosure.lean');
  if (!existsSync(reachSource)) errors.push('missing-reach-source');
  const localProofAudit=existsSync(reachSource)
    ? lexicallyAuditLeanSource(readFileSync(reachSource,'utf8'), { requireProbes:true }) : null;
  for (const token of localProofAudit?.forbiddenTokens ?? [])
    errors.push('local-axiom-law:' + token);
  return {
    status: errors.length ? 'blocked' : 'source-mounts-present',
    errors, toolchain, lakeDir, dependencies, localProofAudit,
    lakefileSha256: digest(config),
    reachSourceSha256: digest(reachSource),
  };
}

/** The root proof receipt requires Lake success AND fresh kernel axiom readback. */
export function runProofTarget(root, target = 'reach') {
  if (!Object.hasOwn(MODULES, target)) {
    return { status: 'refused', reason: 'unknown-target', target, allowed: Object.keys(MODULES) };
  }
  const preflight = inspectProofWorkspace(root);
  if (preflight.status !== 'source-mounts-present') {
    return { ...preflight, target, attemptedBuild: false };
  }
  const args = ['build', ...(MODULES[target] ? [MODULES[target]] : [])];
  const started = process.hrtime.bigint();
  const run = spawnSync('lake', args, {
    cwd: preflight.lakeDir, encoding: 'utf8', timeout: 10 * 60_000,
    maxBuffer: 16 * 1024 * 1024,
  });
  const elapsedMs = Number(process.hrtime.bigint() - started) / 1e6;
  const stdout = run.stdout ?? '';
  const stderr = run.stderr ?? '';
  const compileStatus = run.error?.code === 'ENOENT' ? 'toolchain-unavailable'
    : run.error ? 'execution-error'
      : run.status === 0 ? 'module-build-passed' : 'module-build-failed';
  // A successful build can contain imported sorryAx, Classical.choice or
  // propext; it is NOT sufficient under the actual organizational axiom law.
  // Run fresh Lean #print axioms against the compiled declarations.
  const axiomReadback = compileStatus === 'module-build-passed'
    ? runNativeAxiomAudit(preflight.lakeDir,{
        modules: target === 'all' ? undefined : [target === 'reach' ? 'ReachClosure'
          : target === 'board' ? 'Board'
          : target === 'ko' ? 'Ko'
          : target === 'evidence' ? 'Evidence' : 'Admission'],
      }) : null;
  const status = compileStatus !== 'module-build-passed' ? compileStatus
    : axiomReadback?.status === 'kernel-axiom-policy-passed'
      ? 'module-build-and-axioms-passed' : 'axiom-audit-refused';
  return {
    ...preflight, status, compileStatus, target, command: ['lake', ...args],
    attemptedBuild: true, exitCode: run.status, elapsedMs,
    error: run.error?.message ?? null, axiomReadback,
    stdoutSha256: createHash('sha256').update(stdout).digest('hex'),
    stderrSha256: createHash('sha256').update(stderr).digest('hex'),
    stdoutTail: stdout.slice(-3000), stderrTail: stderr.slice(-3000),
    qualification:'compiled target and fresh kernel transitive-axiom readback only; no Loopflow, source rights or publication gate',
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const target = process.argv[2];
  const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
  const result = target === '--check' || target === undefined
    ? inspectProofWorkspace(root) : runProofTarget(root, target);
  process.stdout.write(JSON.stringify(result, null, 2) + '\n');
  if (!['source-mounts-present', 'module-build-and-axioms-passed'].includes(result.status)) {
    process.exitCode = 1;
  }
}
