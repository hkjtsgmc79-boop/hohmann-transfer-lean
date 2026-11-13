# Sources and provenance — checked 2026-11-13

S1. John E. Prussing, “Simple proof of the global optimality of the Hohmann transfer,” Journal of Guidance, Control, and Dynamics 15 (1992). NASA NTRS record 19920064136 explicitly limits the result to the class of two-impulse transfers between coplanar circular orbits. The NASA record has no downloadable full text; only its abstract/metadata were used.
https://ntrs.nasa.gov/citations/19920064136

S2. Yiqun Zhang and Junyan Xu, “Hohmann Transfer via Constrained Optimization,” arXiv:1712.01512v1 (2017), especially Introduction and Section 2. The paper explicitly defines global as all possible two-impulse coplanar transfers and formulates the energy/angular-momentum endpoint constraints. Its introduction credits prior results establishing separate impulse minima. We use an algebraic gap-certificate implementation rather than formalizing its KKT proof.
https://arxiv.org/html/1712.01512v1

S3. Devendra Ghate, “The Hohmann Transfer,” author course note (dated 2026-11-05). A supplementary original teaching source for the invariant-coordinate viewpoint and clear class restriction; not the basis for a novel-priority claim.
https://devendra-ghate.github.io/courses/sfm/sfm-slides/hohmann-transfer.html

S4. “Two-impulse, bi-parabolic, and bi-elliptical transfers between coplanar elliptical orbits,” Acta Astronautica (2020), publisher abstract/metadata. Context for distinguishing two- and three-impulse optimization. Our concrete 1→64→16 cost, rational certificate and numerical integration are calculated within this delivery, not imported as externally verified proofs.
https://www.sciencedirect.com/science/article/pii/S0094576520303805

S5. NASA Glenn Research Center, “Ideal Rocket Equation.” Basis for the conditional fixed-exhaust-speed interpretation only; H2 does not formalize a complete variable-mass rocket model.
https://www1.grc.nasa.gov/beginners-guide-to-aeronautics/ideal-rocket-equation/

S6. Mathlib official calculus and square-root documentation. Used to ground API choices; current documentation alone does not establish compatibility with the pinned historical commit.
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/Calculus/MeanValue.html
https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.html

Code dependency: Lean4.30.0, Mathlib c5ea00351c28e24afc9f0f84379aa41082b1188f, inherited from the user's prior working baseline. This runtime has no Lean. No independent compiler verification was obtained.

H1 provenance: attached Hohmann_Transfer_H1.zip preserved in baseline/. Its12 modular proof sources were copied byte-for-byte, checked by a real automated test. It remains an uncompiled source baseline, not a proof certificate.

AI disclosure: H2 mathematical derivations, Lean candidates, tools and documentation were generated with AI assistance. A human submitting any upstream contribution must review the theorem semantics, code, sources and build evidence and take responsibility for the contribution. No upstream submission has been made in this round.
