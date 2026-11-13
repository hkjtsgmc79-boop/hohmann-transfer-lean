/-
Copyright (c) 2026 Chengyuan AI Lab. Released under Apache 2.0.
Authors: Qianli Ma
-/
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Tactic

noncomputable section
namespace HohmannOptimality

/-- Reciprocal radius ratio. Length unit is r₁; speed unit is √(μ/r₁). -/
structure Shape where
  alpha : ℝ
  alpha_pos : 0 < alpha
  alpha_lt_one : alpha < 1

namespace Shape

def circularOuter (s : Shape) : ℝ := Real.sqrt s.alpha
def hH (s : Shape) : ℝ := Real.sqrt (2 / (1 + s.alpha))
def energyH (s : Shape) : ℝ := s.hH ^ 2 - 2
/-- The conserved energy variable is twice specific energy in speed units. -/
def burnH₁ (s : Shape) : ℝ := s.hH - 1
def burnH₂ (s : Shape) : ℝ := s.circularOuter - s.alpha * s.hH
def costH (s : Shape) : ℝ := s.burnH₁ + s.burnH₂

lemma sum_pos (s : Shape) : 0 < 1 + s.alpha := by linarith [s.alpha_pos]
lemma c_pos (s : Shape) : 0 < s.circularOuter := Real.sqrt_pos.2 s.alpha_pos
lemma c_sq (s : Shape) : s.circularOuter ^ 2 = s.alpha :=
  Real.sq_sqrt (le_of_lt s.alpha_pos)
lemma c_lt_one (s : Shape) : s.circularOuter < 1 := by
  nlinarith [s.c_sq, s.alpha_lt_one, s.c_pos]
lemma h_pos (s : Shape) : 0 < s.hH :=
  Real.sqrt_pos.2 (div_pos (by norm_num) s.sum_pos)
lemma h_sq (s : Shape) : s.hH ^ 2 = 2 / (1 + s.alpha) :=
  Real.sq_sqrt (le_of_lt (div_pos (by norm_num) s.sum_pos))
lemma h_sq_mul (s : Shape) : s.hH ^ 2 * (1 + s.alpha) = 2 := by
  rw [s.h_sq]
  field_simp [ne_of_gt s.sum_pos]
lemma one_lt_h_sq (s : Shape) : 1 < s.hH ^ 2 := by
  rw [s.h_sq]
  apply (lt_div_iff₀ s.sum_pos).2
  linarith [s.alpha_lt_one]
lemma one_lt_h (s : Shape) : 1 < s.hH := by
  nlinarith [s.one_lt_h_sq, s.h_pos]
lemma alpha_h_sq_lt_one (s : Shape) : s.alpha * s.hH ^ 2 < 1 := by
  nlinarith [s.h_sq_mul, s.one_lt_h_sq]
lemma alpha_h_lt_c (s : Shape) : s.alpha * s.hH < s.circularOuter := by
  have hmul := mul_lt_mul_of_pos_left s.alpha_h_sq_lt_one s.alpha_pos
  have hp : 0 < s.alpha * s.hH := mul_pos s.alpha_pos s.h_pos
  nlinarith [s.c_sq, s.c_pos]
lemma alpha_c_lt_one (s : Shape) : s.alpha * s.circularOuter < 1 := by
  have h := mul_lt_mul_of_pos_right s.alpha_lt_one s.c_pos
  nlinarith [s.c_lt_one]
lemma alpha_sq_h_lt_one (s : Shape) : s.alpha ^ 2 * s.hH < 1 := by
  have h := mul_lt_mul_of_pos_left s.alpha_h_lt_c s.alpha_pos
  nlinarith [s.alpha_c_lt_one]
lemma alpha_c_lt_h (s : Shape) : s.alpha * s.circularOuter < s.hH :=
  lt_trans s.alpha_c_lt_one s.one_lt_h
lemma corner_inner (s : Shape) : s.energyH + 2 = s.hH ^ 2 := by
  unfold energyH
  ring
lemma corner_outer (s : Shape) : s.energyH + 2 * s.alpha = s.alpha ^ 2 * s.hH ^ 2 := by
  have h := congrArg (fun z : ℝ => (s.alpha - 1) * z) s.h_sq_mul
  unfold energyH
  nlinarith
lemma corner_relation (s : Shape) :
    s.alpha ^ 2 * s.hH ^ 2 - 2 * s.alpha = s.hH ^ 2 - 2 := by
  have h := s.corner_outer
  dsimp [energyH] at h
  linarith
lemma burnH₁_pos (s : Shape) : 0 < s.burnH₁ := sub_pos.mpr s.one_lt_h
lemma burnH₂_pos (s : Shape) : 0 < s.burnH₂ := sub_pos.mpr s.alpha_h_lt_c
lemma costH_pos (s : Shape) : 0 < s.costH := add_pos s.burnH₁_pos s.burnH₂_pos

/-- Both radial-speed squares must be nonnegative. h is signed: retrograde
coasts are not silently excluded. This is a relaxation, not a trajectory. -/
def Feasible (s : Shape) (w h : ℝ) : Prop :=
  h ^ 2 ≤ w + 2 ∧ s.alpha ^ 2 * h ^ 2 ≤ w + 2 * s.alpha

lemma corner_feasible (s : Shape) : s.Feasible s.energyH s.hH := by
  constructor
  · exact le_of_eq s.corner_inner.symm
  · exact le_of_eq s.corner_outer.symm

def burnSquare₁ (s : Shape) (w h : ℝ) : ℝ := w + 3 - 2 * h
def burnSquare₂ (s : Shape) (w h : ℝ) : ℝ :=
  w + 3 * s.alpha - 2 * s.alpha * s.circularOuter * h

end Shape
end HohmannOptimality
