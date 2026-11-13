"""Source packaging and axiom-log helpers. These are not formal proof validators."""
from __future__ import annotations
import hashlib
from pathlib import Path
import re

CORE_MODULES = ['Shape','EndpointBounds','EndpointOptimality','PhysicalUnits','PlanarState',
                'KeplerConservation','Bielliptic','Fuel','PublicStatement']
BRIDGE_MODULES = ['H1Bridge','BiellipticWitness']
H1_MODULES = ['Parameters','Plane','Geometry','KeplerClock','Differentiation','Dynamics',
              'Circular','Endpoints','Impulses','Invariants','Transfer','PublicStatement']
MODULES = CORE_MODULES + BRIDGE_MODULES
ALLOWED_AXIOMS = {'propext','Classical.choice','Quot.sound'}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def strip_comments_strings(text: str) -> str:
    """Conservative lexical scan, preserving newlines. Not a Lean parser."""
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; out.extend('  '); i+=2
            elif text.startswith('-/',i): depth-=1; out.extend('  '); i+=2
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif string:
            if text[i]=='\\': out.extend('  '); i+=2
            elif text[i]=='"': string=False; out.append(' '); i+=1
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text.startswith('/-',i): depth=1; out.extend('  '); i+=2
        elif text.startswith('--',i):
            end=text.find('\n',i)
            if end<0: end=len(text)
            out.extend(' '*(end-i)); i=end
        elif text[i]=='"': string=True; out.append(' '); i+=1
        else: out.append(text[i]); i+=1
    if depth or string: raise ValueError('Unterminated comment/string; not safe to scan.')
    return ''.join(out)


def inventory(root: Path) -> dict:
    files=[]; forbidden=[]; declarations=0
    for name in MODULES:
        p=root/'HohmannOptimality'/f'{name}.lean'
        text=p.read_text(); clean=strip_comments_strings(text)
        ds=re.findall(r'\b(?:lemma|theorem)\s+([\w\u0080-\uffff]+)',clean)
        bad=re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|sorryAx)\b',clean)
        declarations+=len(ds)
        files.append({'path':str(p.relative_to(root)),'sha256':sha256(p),'lines':len(text.splitlines()),'declarations':ds})
        forbidden.extend({'file':str(p.relative_to(root)),'token':x} for x in bad)
    return {'kind':'text inventory only; not Lean parsing or verification','modules':len(MODULES),
            'declarations':declarations,'lines':sum(x['lines'] for x in files),'files':files,'forbidden_tokens':forbidden}


def generate_exports(root: Path) -> None:
    """Mechanically export without claiming compilation or introducing proof terms."""
    groups={
      'Hohmann_Transfer_H2_Core_All.lean': [('HohmannOptimality',n) for n in CORE_MODULES],
      'Hohmann_Transfer_H2_All.lean': [('HohmannTransfer',n) for n in H1_MODULES]+
          [('HohmannOptimality',n) for n in MODULES],
    }
    for filename,modules in groups.items():
        bodies=[]; imports=[]
        for directory,n in modules:
            source=(root/directory/f'{n}.lean').read_text()
            for line in source.splitlines():
                if line.startswith('import Mathlib') and line not in imports: imports.append(line)
            body='\n'.join(line for line in source.splitlines() if not line.startswith('import '))
            bodies.append(f'\n-- SOURCE MODULE: {directory}/{n}.lean\n'+body)
        (root/filename).write_text('/- Generated mechanically from the modular Hohmann sources. -/\n'+'\n'.join(imports)+'\n'+
                                   '\n'.join(bodies)+'\n')
    paths=['lean-toolchain','lakefile.toml','HohmannOptimality.lean','HohmannOptimalityPhysical.lean']
    paths += [f'HohmannOptimality/{n}.lean' for n in MODULES]
    paths += ['Audit.lean','AuditPhysical.lean','ApiProbe.lean','Examples.lean']
    (root/'Hohmann_Transfer_H2_Source.txt').write_text(
        'H2 NEW SOURCE — UNCOMPILED CANDIDATES (H1 baseline included separately)\n\n'+
        '\n'.join('='*72+'\nFILE: '+f+'\n'+'='*72+'\n'+(root/f).read_text() for f in paths))


def parse_axioms(text: str, expected: list[str]) -> dict:
    records={}
    for name,items in re.findall(r"'([^']+)'\s+depends on axioms:\s*\[([^\]]*)\]",text,re.S):
        records[name]=[x.strip() for x in items.split(',') if x.strip()]
    for name in re.findall(r"'([^']+)'\s+does not depend on any axioms",text): records[name]=[]
    missing=[name for name in expected if name not in records]
    unexpected={name:[x for x in xs if x not in ALLOWED_AXIOMS] for name,xs in records.items()}
    unexpected={name:xs for name,xs in unexpected.items() if xs}
    return {'passed':not missing and not unexpected and len(records)==len(expected),
            'records':records,'missing':missing,'unexpected_axioms':unexpected}


def public_signatures(text: str) -> dict[str, str]:
    """Freeze textual theorem headers, allowing proof-body repairs. Not a Lean parser.

    This H1 public file has no let-bindings or local definitions in theorem headers.
    The archived full source remains the reference for human semantic review.
    """
    clean = strip_comments_strings(text)
    result = {}
    for match in re.finditer(r"\btheorem\s+([\w\u0080-\uffff]+)", clean):
        end = clean.find(":=", match.end())
        if end < 0:
            raise ValueError("Missing proof delimiter in public theorem")
        result[match.group(1)] = clean[match.start():end].strip()
    return result
