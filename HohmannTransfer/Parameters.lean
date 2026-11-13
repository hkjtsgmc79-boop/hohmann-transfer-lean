/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic

noncomputable section
namespace HohmannTransfer

/-! # Physical inputs and derived ellipse parameters
The input contains only μ, two radii, and physical inequalities.
No conservation law, orbit equation or optimality assertion is an input.
The first milestone treats outward, coplanar transfers, 0 < r₁ < r₂.
-/
structure Parameters where
  mu : ℝ
  r₁ : ℝ
  r₂ : ℝ
  mu_pos : 0 < mu
  r₁_pos : 0 < r₁
  outward : r₁ < r₂

namespace Parameters

def a (p : Parameters) : ℝ := (p.r₁ + p.r₂) / 2
def e (p : Parameters) : ℝ := (p.r₂ - p.r₁) / (p.r₁ + p.r₂)
def b (p : Parameters) : ℝ := Real.sqrt (p.r₁ * p.r₂)
def n (p : Parameters) : ℝ := Real.sqrt (p.mu / p.a ^ 3)
def transferTime (p : Parameters) : ℝ := Real.pi / p.n

lemma r₂_pos (p : Parameters) : 0 < p.r₂ := lt_trans p.r₁_pos p.outward
lemma sum_pos (p : Parameters) : 0 < p.r₁ + p.r₂ := add_pos p.r₁_pos p.r₂_pos
lemma a_pos (p : Parameters) : 0 < p.a := div_pos p.sum_pos (by norm_num)
lemma e_pos (p : Parameters) : 0 < p.e := div_pos (sub_pos.mpr p.outward) p.sum_pos
lemma e_lt_one (p : Parameters) : p.e < 1 := by
  unfold e
  apply (div_lt_one p.sum_pos).2
  linarith [p.r₁_pos]
lemma b_pos (p : Parameters) : 0 < p.b :=
  Real.sqrt_pos.2 (mul_pos p.r₁_pos p.r₂_pos)
lemma b_sq (p : Parameters) : p.b ^ 2 = p.r₁ * p.r₂ :=
  Real.sq_sqrt (le_of_lt (mul_pos p.r₁_pos p.r₂_pos))
lemma n_pos (p : Parameters) : 0 < p.n :=
  Real.sqrt_pos.2 (div_pos p.mu_pos (pow_pos p.a_pos 3))
lemma n_sq (p : Parameters) : p.n ^ 2 = p.mu / p.a ^ 3 :=
  Real.sq_sqrt (le_of_lt (div_pos p.mu_pos (pow_pos p.a_pos 3)))
lemma a_ne (p : Parameters) : p.a ≠ 0 := ne_of_gt p.a_pos
lemma n_ne (p : Parameters) : p.n ≠ 0 := ne_of_gt p.n_pos
lemma r₁_ne (p : Parameters) : p.r₁ ≠ 0 := ne_of_gt p.r₁_pos
lemma r₂_ne (p : Parameters) : p.r₂ ≠ 0 := ne_of_gt p.r₂_pos
lemma one_sub_e_pos (p : Parameters) : 0 < 1 - p.e := sub_pos.mpr p.e_lt_one
lemma one_add_e_pos (p : Parameters) : 0 < 1 + p.e := by linarith [p.e_pos]
lemma a_mul_one_sub_e (p : Parameters) : p.a * (1 - p.e) = p.r₁ := by
  unfold a e
  field_simp [ne_of_gt p.sum_pos]
  <;> ring
lemma a_mul_one_add_e (p : Parameters) : p.a * (1 + p.e) = p.r₂ := by
  unfold a e
  field_simp [ne_of_gt p.sum_pos]
  <;> ring
lemma b_sq_ellipse (p : Parameters) : p.b ^ 2 = p.a ^ 2 * (1 - p.e ^ 2) := by
  rw [p.b_sq]
  unfold a e
  field_simp [ne_of_gt p.sum_pos]
  <;> ring
lemma n_sq_mul_a_cube (p : Parameters) : p.n ^ 2 * p.a ^ 3 = p.mu := by
  rw [p.n_sq]
  field_simp [p.a_ne]
lemma transferTime_pos (p : Parameters) : 0 < p.transferTime :=
  div_pos Real.pi_pos p.n_pos
lemma transferTime_sq (p : Parameters) :
    p.transferTime ^ 2 * p.mu = Real.pi ^ 2 * p.a ^ 3 := by
  have hn := p.n_sq_mul_a_cube
  unfold transferTime
  field_simp [p.n_ne]
  nlinarith [congrArg (fun x : ℝ => Real.pi ^ 2 * x) hn]
lemma transferTime_eq (p : Parameters) :
    p.transferTime = Real.pi * Real.sqrt (p.a ^ 3 / p.mu) := by
  have hr := Real.sq_sqrt (le_of_lt (div_pos (pow_pos p.a_pos 3) p.mu_pos))
  have hroot := Real.sqrt_nonneg (p.a ^ 3 / p.mu)
  have ht := p.transferTime_sq
  have hμ := p.mu_pos
  have htpos := p.transferTime_pos
  have hproduct := mul_nonneg (le_of_lt Real.pi_pos) hroot
  have hs : p.transferTime ^ 2 =
      (Real.pi * Real.sqrt (p.a ^ 3 / p.mu)) ^ 2 := by
    rw [mul_pow, hr, ← mul_div_assoc]
    exact (eq_div_iff (ne_of_gt hμ)).2 ht
  nlinarith

end Parameters

end HohmannTransfer
