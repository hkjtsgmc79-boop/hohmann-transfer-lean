/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/
import HohmannTransfer.Endpoints
import HohmannTransfer.Circular

noncomputable section
namespace HohmannTransfer

/-! # Two velocity jumps, including vector directions
At the opposite end of the ellipse, prograde points toward negative y.
A positive second burn magnitude must NOT be implemented as a +y vector.
-/
def deltaV₁ (p : Parameters) : ℝ := periSpeed p - circularSpeed p.mu p.r₁
def deltaV₂ (p : Parameters) : ℝ := circularSpeed p.mu p.r₂ - apoSpeed p
def totalDeltaV (p : Parameters) : ℝ := deltaV₁ p + deltaV₂ p
def entryImpulse (p : Parameters) : ℂ :=
  velocity p 0 - pack 0 (circularSpeed p.mu p.r₁)
def exitImpulse (p : Parameters) : ℂ :=
  pack 0 (-circularSpeed p.mu p.r₂) - velocity p p.transferTime

lemma peri_excess_sq (p : Parameters) :
    periSpeed p ^ 2 - circularSpeed p.mu p.r₁ ^ 2 =
      p.mu*(p.r₂-p.r₁)/(p.r₁*(p.r₁+p.r₂)) := by
  rw [periSpeed_sq, circularSpeed_sq p.mu_pos p.r₁_pos]
  field_simp [p.r₁_ne, ne_of_gt p.sum_pos]
  <;> ring
lemma apo_deficit_sq (p : Parameters) :
    circularSpeed p.mu p.r₂ ^ 2 - apoSpeed p ^ 2 =
      p.mu*(p.r₂-p.r₁)/(p.r₂*(p.r₁+p.r₂)) := by
  rw [apoSpeed_sq, circularSpeed_sq p.mu_pos p.r₂_pos]
  field_simp [p.r₂_ne, ne_of_gt p.sum_pos]
  <;> ring
lemma deltaV₁_pos (p : Parameters) : 0 < deltaV₁ p := by
  have hs := peri_excess_sq p
  have hc := circularSpeed_pos p.mu_pos p.r₁_pos
  have hp := periSpeed_pos p
  have hd : 0 < p.mu*(p.r₂-p.r₁)/(p.r₁*(p.r₁+p.r₂)) :=
    div_pos (mul_pos p.mu_pos (sub_pos.mpr p.outward)) (mul_pos p.r₁_pos p.sum_pos)
  unfold deltaV₁
  nlinarith
lemma deltaV₂_pos (p : Parameters) : 0 < deltaV₂ p := by
  have hs := apo_deficit_sq p
  have hc := circularSpeed_pos p.mu_pos p.r₂_pos
  have hp := apoSpeed_pos p
  have hd : 0 < p.mu*(p.r₂-p.r₁)/(p.r₂*(p.r₁+p.r₂)) :=
    div_pos (mul_pos p.mu_pos (sub_pos.mpr p.outward)) (mul_pos p.r₂_pos p.sum_pos)
  unfold deltaV₂
  nlinarith
lemma totalDeltaV_pos (p : Parameters) : 0 < totalDeltaV p :=
  add_pos (deltaV₁_pos p) (deltaV₂_pos p)
lemma periSpeed_factorized (p : Parameters) :
    periSpeed p = circularSpeed p.mu p.r₁ * Real.sqrt (2*p.r₂/(p.r₁+p.r₂)) := by
  have hh : 0 < 2*p.r₂/(p.r₁+p.r₂) :=
    div_pos (mul_pos (by norm_num) p.r₂_pos) p.sum_pos
  have hr := Real.sq_sqrt (le_of_lt hh)
  have hc := circularSpeed_sq p.mu_pos p.r₁_pos
  have hp := periSpeed_pos p
  have hq := mul_nonneg (le_of_lt (circularSpeed_pos p.mu_pos p.r₁_pos))
    (Real.sqrt_nonneg (2*p.r₂/(p.r₁+p.r₂)))
  have hs : periSpeed p^2 =
      (circularSpeed p.mu p.r₁ * Real.sqrt (2*p.r₂/(p.r₁+p.r₂)))^2 := by
    rw [periSpeed_sq, mul_pow, hc, hr]
    field_simp [p.r₁_ne, ne_of_gt p.sum_pos]
    <;> ring
  nlinarith
lemma apoSpeed_factorized (p : Parameters) :
    apoSpeed p = circularSpeed p.mu p.r₂ * Real.sqrt (2*p.r₁/(p.r₁+p.r₂)) := by
  have hh : 0 < 2*p.r₁/(p.r₁+p.r₂) :=
    div_pos (mul_pos (by norm_num) p.r₁_pos) p.sum_pos
  have hr := Real.sq_sqrt (le_of_lt hh)
  have hc := circularSpeed_sq p.mu_pos p.r₂_pos
  have hp := apoSpeed_pos p
  have hq := mul_nonneg (le_of_lt (circularSpeed_pos p.mu_pos p.r₂_pos))
    (Real.sqrt_nonneg (2*p.r₁/(p.r₁+p.r₂)))
  have hs : apoSpeed p^2 =
      (circularSpeed p.mu p.r₂ * Real.sqrt (2*p.r₁/(p.r₁+p.r₂)))^2 := by
    rw [apoSpeed_sq, mul_pow, hc, hr]
    field_simp [p.r₂_ne, ne_of_gt p.sum_pos]
    <;> ring
  nlinarith
lemma deltaV₁_formula (p : Parameters) :
    deltaV₁ p = Real.sqrt (p.mu/p.r₁) *
      (Real.sqrt (2*p.r₂/(p.r₁+p.r₂))-1) := by
  rw [deltaV₁, periSpeed_factorized]
  unfold circularSpeed
  ring
lemma deltaV₂_formula (p : Parameters) :
    deltaV₂ p = Real.sqrt (p.mu/p.r₂) *
      (1-Real.sqrt (2*p.r₁/(p.r₁+p.r₂))) := by
  rw [deltaV₂, apoSpeed_factorized]
  unfold circularSpeed
  ring
lemma entryImpulse_eq (p : Parameters) : entryImpulse p = pack 0 (deltaV₁ p) := by
  rw [entryImpulse, velocity_departure]
  apply Complex.ext <;> simp [pack, deltaV₁]
lemma exitImpulse_eq (p : Parameters) : exitImpulse p = pack 0 (-deltaV₂ p) := by
  rw [exitImpulse, velocity_arrival]
  apply Complex.ext <;> simp [pack, deltaV₂] <;> ring
lemma entryImpulse_norm (p : Parameters) : ‖entryImpulse p‖ = deltaV₁ p := by
  rw [entryImpulse_eq, norm_pack_vertical, abs_of_pos (deltaV₁_pos p)]
lemma exitImpulse_norm (p : Parameters) : ‖exitImpulse p‖ = deltaV₂ p := by
  rw [exitImpulse_eq, norm_pack_vertical, abs_neg, abs_of_pos (deltaV₂_pos p)]
lemma totalDeltaV_eq_sum_norms (p : Parameters) :
    totalDeltaV p = ‖entryImpulse p‖ + ‖exitImpulse p‖ := by
  rw [entryImpulse_norm, exitImpulse_norm]
  rfl
lemma impulses_tangential (p : Parameters) :
    (position p 0).re * (entryImpulse p).re +
      (position p 0).im * (entryImpulse p).im = 0 ∧
    (position p p.transferTime).re * (exitImpulse p).re +
      (position p p.transferTime).im * (exitImpulse p).im = 0 := by
  simp [position_departure, position_arrival, entryImpulse_eq, exitImpulse_eq, pack]

end HohmannTransfer
