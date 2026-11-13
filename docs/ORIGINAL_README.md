# Chengyuan AI Lab — Hohmann Transfer H2

**H2: Global two-impulse optimality and a finite three-impulse counterexample.**
Date: 2026-11-13. **All Lean proofs are uncompiled candidates.**

This is NOT a proof that Hohmann beats every possible maneuver. It develops:

1. A global lower bound over all two-impulse, coplanar, co-oriented circular-to-circular transfers, with free phase/time in a fixed Newtonian point-mass field.
2. An equality characterization and a bridge to the explicit H1 orbit attaining the bound.
3. A finite bielliptic witness at radii 1 → 64 → 16 with strictly less delta-v than Hohmann 1 → 16.
4. A conditional ideal-fuel corollary under a fixed positive exhaust speed, not a general spacecraft fuel theorem.

## Start

Read `00_START_HERE.md` and `MATHEMATICAL_SPEC.md`.
Give `01_LOCAL_CODEX_PROMPT.txt` to a local Lean developer/agent.

```bash
bash scripts/verify.sh core --lean /absolute/path/to/lean --mathlib-root /absolute/path/to/mathlib
bash scripts/verify.sh full --lean /absolute/path/to/lean --mathlib-root /absolute/path/to/mathlib
```

`core` checks the new lower bound and exact cost counterexample without the H1 inverse-clock dependency.
`full` additionally rebuilds H1 and the actual-orbit attainment and finite bielliptic witness.
A core PASS is **not** a full physical-witness PASS. Neither has been obtained in this delivery.

## Evidence and files

- `H2_REPORT.md`: progress and actual execution results.
- `MATHEMATICAL_SPEC.md`: complete author derivation, assumptions and equality case.
- `docs/SEMANTIC_CONTRACT.md`: what must remain unchanged during repair.
- `docs/SOURCES.md`: primary literature and provenance.
- `reports/math-checks.json`: independent algebra/numerical checks, NOT Lean verification.
- `reports/tool-tests.log`: 16 runner-tool unit tests.
- `reports/run_core_*/verification.json`: real blocked Lean attempt.
- `HohmannOptimality/`: 11 new proof modules.
- `HohmannTransfer/`: 12 H1 proof modules preserved byte-for-byte.
- `contracts/`: frozen public theorem headers for local repair checks.
- `Hohmann_Transfer_H2_Core_All.lean`: generated standalone core.
- `Hohmann_Transfer_H2_All.lean`: generated full source including H1.
- `baseline/Hohmann_Transfer_H1.zip`: original H1 archival copy.

Do not edit generated single-file exports. Change modular sources, then run `python3 scripts/generate_exports.py`.
The source size is not a correctness metric. A keyword scan is not a kernel proof.
No public submission, priority claim, independent review, or Physlib acceptance is asserted.
