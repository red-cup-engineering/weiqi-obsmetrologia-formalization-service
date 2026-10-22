import { createHash } from 'node:crypto';
import { spawnSync } from 'node:child_process';
import { existsSync, readFileSync } from 'node:fs';
import { dirname, join, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

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
    return { name, declaredPath, absolutePath, sourcePresent };
  });
  const toolchain = existsSync(toolchainFile)
    ? readFileSync(toolchainFile, 'utf8').trim() : null;
  if (existsSync(join(lakeDir, 'WeiqiObsmetrologia', 'ReachClosure.lean')) === false) {
    errors.push('missing-reach-source');
  }
  return {
    status: errors.length ? 'blocked' : 'source-mounts-present',
    errors, toolchain, lakeDir, dependencies,
    lakefileSha256: digest(config),
    reachSourceSha256: digest(join(lakeDir, 'WeiqiObsmetrologia', 'ReachClosure.lean')),
  };
}

/** A build is a proof-tool receipt only when Lake itself returned success. */
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
  const status = run.error?.code === 'ENOENT' ? 'toolchain-unavailable'
    : run.error ? 'execution-error'
      : run.status === 0 ? 'module-build-passed' : 'module-build-failed';
  return {
    ...preflight, status, target, command: ['lake', ...args],
    attemptedBuild: true, exitCode: run.status, elapsedMs,
    error: run.error?.message ?? null,
    stdoutSha256: createHash('sha256').update(stdout).digest('hex'),
    stderrSha256: createHash('sha256').update(stderr).digest('hex'),
    stdoutTail: stdout.slice(-3000), stderrTail: stderr.slice(-3000),
    qualification: 'module-build-only; not an independent axiom, Loopflow or publication gate',
  };
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const target = process.argv[2];
  const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
  const result = target === '--check' || target === undefined
    ? inspectProofWorkspace(root) : runProofTarget(root, target);
  process.stdout.write(JSON.stringify(result, null, 2) + '\n');
  if (!['source-mounts-present', 'module-build-passed'].includes(result.status)) {
    process.exitCode = 1;
  }
}
