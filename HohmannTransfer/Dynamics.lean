/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
import HohmannTransfer.Differentiation

noncomputable section
namespace HohmannTransfer

/-! # Newtonian coast dynamics
Inverse-cube scalar times the displacement vector is the inverse-square force.
The norm denominator is proved nonzero along every point of the coast ellipse.
-/
def gravity (mu : ℝ) (q : ℂ) : ℂ := -(mu/‖q‖^3) • q

lemma norm_position (p : Parameters) (t : ℝ) :
    ‖position p t‖ = radial p (anomaly p t) := norm_ellipse p _
lemma position_bounds (p : Parameters) (t : ℝ) :
    p.r₁ ≤ ‖position p t‖ ∧ ‖position p t‖ ≤ p.r₂ := by
  rw [norm_position]
  exact radial_bounds p _
lemma norm_position_pos (p : Parameters) (t : ℝ) : 0 < ‖position p t‖ := by
  rw [norm_position]
  exact radial_pos p _
lemma position_ne_zero (p : Parameters) (t : ℝ) : position p t ≠ 0 :=
  ellipse_ne_zero p _
lemma acceleration_coefficient (p : Parameters) (u : ℝ) :
    p.n^2/(D p u)^3 = p.mu/(radial p u)^3 := by
  rw [p.n_sq]
  unfold radial
  field_simp [p.a_ne, D_ne p u]
lemma hasDerivAt_velocity_newton (p : Parameters) (t : ℝ) :
    HasDerivAt (velocity p) (gravity p.mu (position p t)) t := by
  convert hasDerivAt_velocity p t using 1
  rw [gravity, norm_position, acceleration_coefficient]
lemma second_deriv_position (p : Parameters) (t : ℝ) :
    deriv (deriv (position p)) t = -(p.mu/‖position p t‖^3) • position p t := by
  rw [deriv_position]
  exact (hasDerivAt_velocity_newton p t).deriv
lemma position_periodic (p : Parameters) :
    Function.Periodic (position p) (2*p.transferTime) := by
  intro t
  unfold position
  rw [anomaly_add_period]
  exact ellipse_periodic p _
lemma velocity_periodic (p : Parameters) :
    Function.Periodic (velocity p) (2*p.transferTime) := by
  intro t
  unfold velocity
  rw [anomaly_add_period]
  apply Complex.ext <;>
    simp [velocityAtAnomaly, D, Real.sin_add_two_pi, Real.cos_add_two_pi]

end HohmannTransfer
