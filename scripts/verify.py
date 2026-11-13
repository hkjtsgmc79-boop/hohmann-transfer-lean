#!/usr/bin/env python3
"""Build H2 with existing Lean 4.35.0 + clean pinned Mathlib. No installation/network.
core: new optimality, dynamics-to-bounds, exact comparison; independent of H1.
full: also recompile all H1 modules and physical attainment/counterexample bridges.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import json, os
from pathlib import Path
import re, shutil, subprocess, sys, time, zipfile
from build_support import (CORE_MODULES, BRIDGE_MODULES, H1_MODULES, generate_exports,
                           inventory, parse_axioms, sha256, public_signatures, strip_comments_strings)
ROOT=Path(__file__).resolve().parents[1]
LOCK=json.loads((ROOT/'dependency-lock.json').read_text())
PIN=LOCK['mathlib_commit']
PUBLIC=['PublicStatement','H1Bridge','BiellipticWitness']


def main() -> int:
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('scope',choices=['core','full'],nargs='?',default='core')
    parser.add_argument('--lean',default=os.environ.get('LEAN_BIN'))
    parser.add_argument('--mathlib-root',default=os.environ.get('MATHLIB_ROOT'))
    parser.add_argument('--timeout',type=int,default=600)
    args=parser.parse_args()
    runid=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=ROOT/'reports'/f'run_{args.scope}_{runid}';out.mkdir(parents=True)
    build=ROOT/'.build-local'/runid;build.mkdir(parents=True)
    report={'run_id':runid,'scope':args.scope,'status':'BLOCKED','lean_verified':False,
            'physical_attainment_verified':False,'commands':[],'expected_mathlib':PIN,
            'started_utc':datetime.now(timezone.utc).isoformat()}
    env=os.environ.copy()
    def source_paths():
        return [p for p in ROOT.rglob('*.lean') if not any(t in p.parts for t in ['.lake','.build-local'])]
    def command(tag,cmd):
        st=time.monotonic()
        try:
            r=subprocess.run(cmd,cwd=ROOT,env=env,text=True,stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT,timeout=args.timeout)
            code,text=r.returncode,r.stdout
        except subprocess.TimeoutExpired as e:
            code=124; text=e.stdout or ''
            if isinstance(text,bytes):text=text.decode(errors='replace')
            text+='\nTIMEOUT\n'
        except OSError as e: code=127;text=str(e)+'\n'
        log=out/f'{tag}.log';log.write_text(text)
        report['commands'].append({'tag':tag,'argv':cmd,'exit_code':code,
                'seconds':time.monotonic()-st,'log':log.name,'sha256':sha256(log)})
        print(f'{tag}: exit={code}',flush=True)
        return code,text
    try:
        generate_exports(ROOT)
        inv=inventory(ROOT);(out/'source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
        report['source_hashes']={str(p.relative_to(ROOT)):sha256(p) for p in source_paths()}
        forbidden=[]
        for p in source_paths():
            for tok in re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx)\b',strip_comments_strings(p.read_text())):
                forbidden.append({'file':str(p.relative_to(ROOT)),'token':tok})
        if forbidden:
            report['forbidden_tokens']=forbidden
            raise RuntimeError('FAIL: proof-bypass keywords present; lexical check is not a full proof audit.')
        for name in PUBLIC:
            frozen=public_signatures((ROOT/'contracts'/f'{name}_H2.lean.txt').read_text())
            current=public_signatures((ROOT/'HohmannOptimality'/f'{name}.lean').read_text())
            current={k:v.replace('Bielliptic.«example»','Bielliptic.example') for k,v in current.items()}
            if any(current.get(k)!=v for k,v in frozen.items()):
                raise RuntimeError(f'FAIL: original public theorem headers changed: {name}.')
        lean=args.lean or shutil.which('lean')
        if not lean:raise RuntimeError('BLOCKED: Lean executable not found; no Lean compilation ran.')
        lean=str(Path(lean).expanduser().resolve())
        code,text=command('lean-version',[lean,'--version'])
        if code or not re.search(r'\bversion\s+4\.35\.0(?:\s|,|\))',text):
            raise RuntimeError('BLOCKED: this branch expects Lean 4.35.0.')
        mr=Path(args.mathlib_root).expanduser().resolve() if args.mathlib_root else ROOT/'.lake/packages/mathlib'
        if not (mr/'.lake/build/lib/lean').is_dir():raise RuntimeError('BLOCKED: compiled Mathlib cache unavailable.')
        code,text=command('mathlib-commit',['git','-C',str(mr),'rev-parse','HEAD'])
        if code or text.strip()!=PIN:raise RuntimeError('BLOCKED: Mathlib commit is not the pinned baseline.')
        code,text=command('mathlib-status',['git','--no-optional-locks','-C',str(mr),'status','--porcelain','--untracked-files=no'])
        if code or text.strip():raise RuntimeError('BLOCKED: Mathlib checkout contains tracked changes.')
        manifest=json.loads((mr/'lake-manifest.json').read_text())
        pins={'mathlib': PIN, **{p['name']:p['rev'] for p in manifest['packages']}}
        report['dependency_pins']=pins
        if pins!=LOCK['packages']:
            raise RuntimeError('BLOCKED: Mathlib manifest disagrees with the Physlib dependency pins.')
        paths=[build,mr/'.lake/build/lib/lean']
        # Lake checkouts place Mathlib and its dependencies side by side.
        for name, rev in pins.items():
            if name=='mathlib': continue
            local=mr.parent/name
            if not local.is_dir():
                local=mr/'.lake/packages'/name
            if not local.is_dir():
                raise RuntimeError(f'BLOCKED: missing checkout of {name}.')
            code,text=command(f'pin-{name}',['git','-C',str(local),'rev-parse','HEAD'])
            if code or text.strip()!=rev:
                raise RuntimeError(f'BLOCKED: {name} checkout differs from Physlib pin.')
            code,text=command(f'status-{name}',['git','--no-optional-locks','-C',str(local),
                                               'status','--porcelain','--untracked-files=no'])
            if code or text.strip():
                raise RuntimeError(f'BLOCKED: {name} checkout contains tracked changes.')
            lib=local/'.lake/build/lib/lean'
            if lib.is_dir(): paths.append(lib)
        report['physlib_reference_commit']=LOCK['physlib_reference_commit']
        lake=str(Path(lean).with_name('lake'))
        code,text=command('lake-version',[lake,'--version'])
        if code or 'Lean version 4.35.0' not in text:
            raise RuntimeError('BLOCKED: expected Lake bundled with Lean 4.35.0.')
        env['LEAN_PATH']=os.pathsep.join(map(str,paths))
        report.update(mathlib_root=str(mr),lean_path=env['LEAN_PATH'])
        seq=[('ApiProbe','ApiProbe.lean')]
        seq += [(n,f'HohmannOptimality/{n}.lean') for n in CORE_MODULES]
        seq += [('core-root','HohmannOptimality.lean'),('examples','Examples.lean'),
                ('core-single','Hohmann_Transfer_H2_Core_All.lean'),('core-axioms','Audit.lean')]
        if args.scope=='full':
            seq += [(f'H1-{n}',f'HohmannTransfer/{n}.lean') for n in H1_MODULES]
            seq += [('H1-root','HohmannTransfer.lean')]
            seq += [(n,f'HohmannOptimality/{n}.lean') for n in BRIDGE_MODULES]
            seq += [('physical-root','HohmannOptimalityPhysical.lean'),
                    ('full-single','Hohmann_Transfer_H2_All.lean'),('physical-axioms','AuditPhysical.lean'),
                    ('all-axioms','AuditFull.lean')]
        for tag,rel in seq:
            dst=build/Path(rel).with_suffix('.olean');dst.parent.mkdir(parents=True,exist_ok=True)
            code,text=command(tag,[lean,'-j2','-o',str(dst),'-i',str(dst.with_suffix('.ilean')),rel])
            if code or re.search(r"declaration uses ['`]?sorry|\bsorryAx\b",text):
                report['failed_stage']=tag;raise RuntimeError(f'FAIL: {tag}. Preserve log; repair proofs, not specifications.')
            if 'axioms' in tag:
                expected=re.findall(r'^#print axioms (\S+)',(ROOT/rel).read_text(),re.M)
                expected=[name.replace('«example»', 'example') for name in expected]
                audit=parse_axioms(text,expected)
                (out/f'{tag}.json').write_text(json.dumps(audit,indent=2)+'\n')
                if not audit['passed']:raise RuntimeError(f'FAIL: {tag} missing or nonstandard dependencies.')
        report.update(status='PASS',lean_verified=True,physical_attainment_verified=args.scope=='full')
    except (RuntimeError,ValueError) as e:
        msg=str(e);report['reason']=msg
        report['status']='FAIL' if msg.startswith('FAIL:') else 'BLOCKED'
        print(msg,flush=True)
    except Exception as e:
        report.update(status='FAIL',reason=f'Runner exception {type(e).__name__}: {e}')
        print(report['reason'],flush=True)
    finally:
        report['finished_utc']=datetime.now(timezone.utc).isoformat()
        report['source_hashes_after']={str(p.relative_to(ROOT)):sha256(p) for p in source_paths()}
        if report.get('source_hashes')!=report['source_hashes_after']:
            report.update(status='FAIL',lean_verified=False,physical_attainment_verified=False,
                          reason='Source changed during verification run.')
        (out/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
        package=ROOT/'reports'/f'Hohmann_Transfer_H2_return_{args.scope}_{runid}.zip'
        with zipfile.ZipFile(package,'w',zipfile.ZIP_DEFLATED) as z:
            for p in ROOT.rglob('*'):
                if not p.is_file() or any(t in p.parts for t in ['.lake','.build-local','__pycache__','.git']):continue
                if 'reports' in p.relative_to(ROOT).parts:continue
                z.write(p,'project/'+str(p.relative_to(ROOT)))
            for p in out.iterdir():
                if p.is_file():z.write(p,'verification/'+p.name)
        print(f'RESULT: {report["status"]}\nReturn package: {package}',flush=True)
    return {'PASS':0,'FAIL':1,'BLOCKED':2}[report['status']]

if __name__=='__main__':sys.exit(main())
