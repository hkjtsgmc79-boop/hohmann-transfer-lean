/- H2 uncompiled candidate. Freeze theorem headers before local repair. -/
import HohmannOptimality.Fuel

noncomputable section
namespace HohmannOptimality

/-- Global means all feasible TWO-impulse, coplanar, co-oriented circle-to-circle
transfers, with free departure phase and flight time. A coast may have radial
velocity, negative momentum, or nonnegative energy. No third burn is allowed. -/
theorem global_two_impulse_endpoint_optimality (s : Shape) :
    (∀ z : EndpointData s, s.costH ≤ z.cost) ∧
    (hohmannEndpoints s).cost=s.costH ∧
    (∀ z : EndpointData s, z.cost=s.costH →
      z.tangent₁=s.hH ∧ z.tangent₂=s.alpha*s.hH ∧
      z.radial₁=0 ∧ z.radial₂=0) := by
  exact ⟨endpoint_total_lower_bound s, hohmannEndpoints_cost s,
    endpoint_equality_characterization s⟩

/-- The global inequality applies to genuinely differentiable Newtonian coast
arcs; conservation is proved in KeplerConservation rather than postulated. -/
theorem global_two_impulse_newton_lower_bound (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂) :
    p.bound ≤ (a.state a.t₀).impulse p.speed+(a.state a.t₁).impulse p.circular₂ :=
  KeplerArc.newton_arc_lower_bound p a h₀ h₁

/-- An unrestricted all-maneuver assertion is false: a finite 1→64→16
bielliptic construction has strictly smaller delta-v than Hohmann 1→16. -/
theorem finite_three_impulse_counterexample :
    (9/1000 : ℝ) < Bielliptic.hohmannCost 16 - Bielliptic.cost Bielliptic.«example» :=
  Bielliptic.finite_bielliptic_saves_deltaV

end HohmannOptimality
