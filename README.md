# Hohmann Transfer and Two-Impulse Optimality in Lean

**Qianli Ma (马千里)** · Chengyuan AI Lab (骋原 AI 实验室)

This project formalizes the outward Hohmann transfer between coplanar, co-oriented circular orbits in a fixed Newtonian point-mass field.

- **H1** constructs the transfer ellipse, proves the Newtonian equations and conservation laws, and derives the two tangential velocity changes and the transfer time.
- **H2** proves a global lower bound for the sum of the Euclidean norms of the two velocity jumps and shows that H1 attains it. The competing coast can have radial velocity and either sign of angular momentum. The equality result fixes the endpoint velocities.
- **Three-impulse comparison** constructs a finite bi-elliptic transfer at normalized radii `1 → 64 → 16`. Its total Δv is lower than the Hohmann cost by more than `9/1000` of the inner circular speed. The fuel corollary assumes an ideal rocket model with fixed positive effective exhaust speed.

The main statements are in [H1 dynamics](HohmannTransfer/PublicStatement.lean), [H2 optimality](HohmannOptimality/PublicStatement.lean), [attainment](HohmannOptimality/H1Bridge.lean), and [the physical counterexample](HohmannOptimality/BiellipticWitness.lean).

## Build and verification

This release uses Lean 4.35.0 and Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. With the pinned Lean toolchain, Git, and Python 3 installed, run from this directory:

```sh
lake exe cache get
bash scripts/verify.sh core
bash scripts/verify.sh full
```

See [build instructions](BUILD_VERIFIED.md) to use an existing Mathlib checkout and build cache. The [verification records](verification/), included in the release ZIP, contain the actual commands, logs, and axiom results. The [Lean 4.30.0 release](https://github.com/hkjtsgmc79-boop/hohmann-transfer-lean/releases/tag/v0.2.0) contains the earlier verification archive. The PhyslibAlpha adaptation is tracked separately in [Physlib Draft PR #2077](https://github.com/leanprover-community/physlib/pull/2077).

AI tools assisted with the Lean formalization and compilation repairs. The code is released under the [Apache 2.0 license](LICENSE).
