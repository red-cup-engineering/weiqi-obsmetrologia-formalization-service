import { createHash } from 'node:crypto';
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { spawnSync } from 'node:child_process';

/**
 * Independent post-build Lean axiom readback for the ORIGINAL Weiqi package.
 * This does not decide proofs by string matching: the Lean kernel elaborates
 * and prints the TRANSITIVE axiom set of each named compiled declaration.
 * The parser only refuses any unread or nonconforming kernel result.
 */
export const ALLOWED_AXIOMS = Object.freeze(['Quot.sound']);
export const PROOF_MODULES = Object.freeze([
  'Board', 'Ko', 'Evidence', 'Admission', 'ReachClosure',
]);

export function declaredAxiomProbes(sourceFiles, moduleNames=PROOF_MODULES) {
  if (!Array.isArray(moduleNames) || moduleNames.length===0 ||
      new Set(moduleNames).size!==moduleNames.length ||
      moduleNames.some(name=>!PROOF_MODULES.includes(name)) ||
      !Array.isArray(sourceFiles) || sourceFiles.length!==moduleNames.length)
    throw new TypeError('axiom audit requires a nonempty set of original modules');
  const probes = [];
  for (let i=0;i<sourceFiles.length;i++) {
    if (typeof sourceFiles[i] !== 'string')
      throw new TypeError('all Lean source modules must be text');
    const matches = [...sourceFiles[i].matchAll(
      /^#print axioms (WeiqiObsmetrologia\.[A-Za-z0-9_.]+)\s*$/gm,
    )].map(m=>m[1]);
    if (matches.length===0)
      throw new TypeError('original module has no axiom probes: '+moduleNames[i]);
    probes.push(...matches);
  }
  if (new Set(probes).size!==probes.length)
    throw new TypeError('duplicate original axiom probe');
  return Object.freeze(probes);
}

/** Machine-parse ONLY Lean's documented two #print-axioms output forms. */
export function auditAxiomReadback(output, expectedNames) {
  if (typeof output!=='string' || !Array.isArray(expectedNames) ||
      expectedNames.length===0 || new Set(expectedNames).size!==expectedNames.length)
    throw new TypeError('axiom readback requires output and unique original names');
  const found = new Map(), duplicate=[], unknown=[];
  const pattern = /'([^'\n]+)' (does not depend on any axioms|depends on axioms: \[([^\]\n]*)\])/g;
  for (const match of output.matchAll(pattern)) {
    const name=match[1];
    const axioms=match[3]===undefined?[]:match[3].split(',').map(x=>x.trim()).filter(Boolean);
    if (!expectedNames.includes(name)) unknown.push(name);
    if (found.has(name)) duplicate.push(name);
    else found.set(name,Object.freeze(axioms));
  }
  const missing=expectedNames.filter(n=>!found.has(n));
  const forbidden=[];
  for (const [name,axioms] of found)
    for (const axiom of axioms)
      if (!ALLOWED_AXIOMS.includes(axiom))
        forbidden.push(Object.freeze({declaration:name,axiom}));
  const passed=!missing.length&&!duplicate.length&&!unknown.length&&!forbidden.length;
  return Object.freeze({
    kind:'weiqi.leanAxiomReadback.v1',
    status:passed?'kernel-axiom-policy-passed':'refused-axiom-evidence',
    expected:expectedNames.length,received:found.size,
    missing:Object.freeze(missing),duplicates:Object.freeze(duplicate),
    unknown:Object.freeze(unknown),forbidden:Object.freeze(forbidden),
    permittedAxioms:ALLOWED_AXIOMS,
    qualification:'transitive-axiom-readback-only; not entire Obsmetrologia Loopflow or source-authority admission',
  });
}

/**
 * Force a FRESH Lean command pass regardless of whether Lake reused a cached
 * .olean. A successful Lake build alone cannot give an axiom-law receipt.
 * A missing toolchain, unparsed output, a single forbidden imported axiom,
 * a truncated report or a compiler error ALL refuse with different statuses.
 */
export function runNativeAxiomAudit(lakeDir, {timeoutMs=600000, modules=PROOF_MODULES}={}) {
  const sourceFiles=modules.map(name=>readFileSync(
    join(lakeDir,'WeiqiObsmetrologia',name+'.lean'),'utf8'));
  const names=declaredAxiomProbes(sourceFiles,modules);
  const importModule=modules.length===1
    ? 'WeiqiObsmetrologia.'+modules[0] : 'WeiqiObsmetrologia';
  const program='import '+importModule+'\n'+
    names.map(name=>'#print axioms '+name).join('\n')+'\n';
  const tmp=mkdtempSync(join(tmpdir(),'weiqi-axiom-audit-'));
  try {
    const file=join(tmp,'Audit.lean');
    writeFileSync(file,program,'utf8');
    const started=process.hrtime.bigint();
    const run=spawnSync('lake',['lean',file],{
      cwd:lakeDir,encoding:'utf8',timeout:timeoutMs,maxBuffer:16*1024*1024,
    });
    const elapsedMs=Number(process.hrtime.bigint()-started)/1e6;
    const stdout=run.stdout??'',stderr=run.stderr??'';
    const output=stdout+'\n'+stderr;
    const analysis=auditAxiomReadback(output,names);
    const status=run.error?.code==='ENOENT'?'lake-unavailable'
      :run.error?'audit-execution-error'
      :run.status!==0?'lean-axiom-command-failed'
      :analysis.status;
    return Object.freeze({
      ...analysis,
      status,sourceModuleCount:modules.length,
      sourceModules:Object.freeze([...modules]),
      command:['lake','lean','<temporary-original-source-axiom-probes>'],
      exitCode:run.status,elapsedMs,error:run.error?.message??null,
      commandSha256:createHash('sha256').update(program).digest('hex'),
      stdoutSha256:createHash('sha256').update(stdout).digest('hex'),
      stderrSha256:createHash('sha256').update(stderr).digest('hex'),
      outputTail:output.slice(-4000),
    });
  } finally {
    rmSync(tmp,{recursive:true,force:true});
  }
}
