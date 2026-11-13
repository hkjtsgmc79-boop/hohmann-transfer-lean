#!/usr/bin/env python3
"""Compare the original and repaired modular declaration texts."""
import argparse
import json
from pathlib import Path
import re
from build_support import strip_comments_strings, sha256

DECLARATION = re.compile(r"^\s*(?:@\[[^\n]+\]\s*)?(?:(?:private|protected|noncomputable) )?"
                         r"(structure|def|abbrev|theorem|lemma)\s+([^\s:(]+)", re.M)
BOUNDARY = re.compile(r"^(?:end\b|namespace\b|noncomputable section\b)", re.M)

def declarations(path):
    source = strip_comments_strings(path.read_text()).replace('«example»', 'example')
    starts = list(DECLARATION.finditer(source))
    output = {}
    for i, match in enumerate(starts):
        stop = starts[i + 1].start() if i + 1 < len(starts) else len(source)
        text = source[match.start():stop].strip()
        boundary = BOUNDARY.search(text)
        if boundary:
            text = text[:boundary.start()]
        kind, name = match.groups()
        if kind in ('theorem', 'lemma'):
            text = text.split(':=', 1)[0]
        elif kind == 'def' and name == 'endpoints' and path.name == 'KeplerConservation.lean':
            # The coordinate fields are data. The final two fields are proof bodies.
            text = text.split('  angular := by', 1)[0]
        output[f'{kind} {name}'] = ' '.join(text.split())
    return output

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('original', type=Path)
    parser.add_argument('current', type=Path)
    args = parser.parse_args()
    results = {'files': {}, 'contracts': {}, 'baseline': {}}
    for subdir in ('HohmannTransfer', 'HohmannOptimality'):
        for original in sorted((args.original / subdir).glob('*.lean')):
            rel = original.relative_to(args.original)
            current = args.current / rel
            old, new = declarations(original), declarations(current)
            results['files'][str(rel)] = {
                'changed': [key for key in old if old[key] != new.get(key)],
                'added': [key for key in new if key not in old],
                'original_sha256': sha256(original),
                'current_sha256': sha256(current),
            }
    for rel in [*(p.relative_to(args.original) for p in (args.original / 'contracts').iterdir()),
                Path('baseline/Hohmann_Transfer_H1.zip')]:
        category = 'baseline' if rel.parts[0] == 'baseline' else 'contracts'
        results[category][str(rel)] = sha256(args.original / rel) == sha256(args.current / rel)
    results['passed'] = (all(not v['changed'] for v in results['files'].values())
                         and all(results['contracts'].values()) and all(results['baseline'].values()))
    print(json.dumps(results, ensure_ascii=False, indent=2))
    return 0 if results['passed'] else 1

if __name__ == '__main__':
    raise SystemExit(main())
