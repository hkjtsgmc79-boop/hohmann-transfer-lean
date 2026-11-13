/- H2 examples: genuine arbitrary competitors, not a numeric replacement. -/
import HohmannOptimality
open HohmannOptimality
noncomputable section

def radiusRatio16 : Shape := ⟨1/16,by norm_num,by norm_num⟩
example (z : EndpointData radiusRatio16) : radiusRatio16.costH ≤ z.cost :=
  endpoint_total_lower_bound _ z
example : (9/1000 : ℝ) < Bielliptic.hohmannCost 16-Bielliptic.cost Bielliptic.«example» :=
  finite_three_impulse_counterexample
example (mu r₁ r₂ : ℝ) (hmu : 0 < mu) (hr : 0 < r₁) (hrr : r₁ < r₂)
    (a : KeplerArc mu)
    (h₀ : (a.state a.t₀).radius=r₁) (h₁ : (a.state a.t₁).radius=r₂) :
    (HohmannOptimality.Units.mk mu r₁ r₂ hmu hr hrr).bound ≤
      (a.state a.t₀).impulse ((HohmannOptimality.Units.mk mu r₁ r₂ hmu hr hrr).speed)+
      (a.state a.t₁).impulse ((HohmannOptimality.Units.mk mu r₁ r₂ hmu hr hrr).circular₂) :=
  global_two_impulse_newton_lower_bound (HohmannOptimality.Units.mk mu r₁ r₂ hmu hr hrr) a h₀ h₁
