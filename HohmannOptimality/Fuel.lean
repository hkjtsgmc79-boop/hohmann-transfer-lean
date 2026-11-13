/-
Authors: Qianli Ma
Delta-v is not generally identical to propellant.
This corollary uses one ideal stage, fixed exhaust speed, same initial mass,
no staging/dry-mass changes/refuelling and no other propellant expenditure.
-/
import HohmannOptimality.KeplerConservation
import HohmannOptimality.Bielliptic

noncomputable section
namespace HohmannOptimality

def idealPropellantFraction (exhaustSpeed deltaV : ℝ) : ℝ :=
  1 - Real.exp (-deltaV/exhaustSpeed)

lemma idealPropellantFraction_mono {ve d₁ d₂ : ℝ} (hve : 0 < ve) (hd : d₁ ≤ d₂) :
    idealPropellantFraction ve d₁ ≤ idealPropellantFraction ve d₂ := by
  have hdiv : -d₂/ve ≤ -d₁/ve :=
    (div_le_div_iff_of_pos_right hve).2 (neg_le_neg hd)
  have he := Real.exp_le_exp.mpr hdiv
  dsimp [idealPropellantFraction]
  linarith

lemma idealPropellantFraction_strict {ve d₁ d₂ : ℝ} (hve : 0 < ve) (hd : d₁ < d₂) :
    idealPropellantFraction ve d₁ < idealPropellantFraction ve d₂ := by
  have hdiv : -d₂/ve < -d₁/ve :=
    (div_lt_div_iff_of_pos_right hve).2 (neg_lt_neg hd)
  have he := Real.exp_lt_exp.mpr hdiv
  dsimp [idealPropellantFraction]
  linarith

/-- Equal exhaust speed makes multiplying burn mass ratios equivalent to using
sum delta-v; this is the ONLY fuel interpretation used here. -/
lemma remaining_fraction_two_burns (ve d₁ d₂ : ℝ) :
    Real.exp (-d₁/ve)*Real.exp (-d₂/ve) = Real.exp (-(d₁+d₂)/ve) := by
  rw [← Real.exp_add]
  congr 1
  ring

theorem newton_arc_ideal_fuel_lower_bound (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂)
    {ve : ℝ} (hve : 0 < ve) :
    idealPropellantFraction ve p.bound ≤ idealPropellantFraction ve
      ((a.state a.t₀).impulse p.speed+(a.state a.t₁).impulse p.circular₂) :=
  idealPropellantFraction_mono hve (KeplerArc.newton_arc_lower_bound p a h₀ h₁)

end HohmannOptimality
