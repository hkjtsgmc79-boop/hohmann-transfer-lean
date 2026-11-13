# Proof dependency map

## core

Shape → EndpointBounds → EndpointOptimality → PhysicalUnits → PlanarState → KeplerConservation
Bielliptic is independent exact transfer-cost algebra (imports Shape).
Fuel imports KeplerConservation and Bielliptic.
PublicStatement imports Fuel.

Main outputs:
- `global_two_impulse_endpoint_optimality`: all relaxed endpoints + equality.
- `global_two_impulse_newton_lower_bound`: every actual Newtonian coast.
- `finite_three_impulse_counterexample`: exact finite cost gap >9/1000.
- `newton_arc_ideal_fuel_lower_bound`: fixed-exhaust-speed ideal model.

## full

All H1 12 modules (Parameters through PublicStatement), then:
- H1Bridge: `h1_global_two_impulse_minimum` identifies H1 achieved delta-v with new global lower bound.
- BiellipticWitness: `physical_three_impulse_counterexample` supplies two genuine Newtonian ellipses, matching finite endpoints, all three impulse norms and exact gap.

These are separable build milestones, not independent reviewed proofs. A core-only result must not be reported as full physical attainment.
