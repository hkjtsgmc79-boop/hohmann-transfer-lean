/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/
import HohmannTransfer.Parameters
import HohmannTransfer.Plane

noncomputable section
namespace HohmannTransfer

/-! # Circular coast orbits before and after the impulses
Each arc has real time derivatives and satisfies the same gravity law.
-/
def circularRate (mu R : ℝ) : ℝ := Real.sqrt (mu/R^3)
def circularSpeed (mu R : ℝ) : ℝ := Real.sqrt (mu/R)
def circularPosition (mu R phase t : ℝ) : ℂ :=
  pack (R*Real.cos (circularRate mu R*t+phase))
    (R*Real.sin (circularRate mu R*t+phase))
def circularVelocity (mu R phase t : ℝ) : ℂ :=
  pack (-R*circularRate mu R*Real.sin (circularRate mu R*t+phase))
    (R*circularRate mu R*Real.cos (circularRate mu R*t+phase))

lemma circularRate_pos {mu R : ℝ} (hm : 0 < mu) (hR : 0 < R) :
    0 < circularRate mu R := Real.sqrt_pos.2 (div_pos hm (pow_pos hR 3))
lemma circularRate_sq {mu R : ℝ} (hm : 0 < mu) (hR : 0 < R) :
    circularRate mu R ^ 2 = mu/R^3 :=
  Real.sq_sqrt (le_of_lt (div_pos hm (pow_pos hR 3)))
lemma circularSpeed_pos {mu R : ℝ} (hm : 0 < mu) (hR : 0 < R) :
    0 < circularSpeed mu R := Real.sqrt_pos.2 (div_pos hm hR)
lemma circularSpeed_sq {mu R : ℝ} (hm : 0 < mu) (hR : 0 < R) :
    circularSpeed mu R ^ 2 = mu/R :=
  Real.sq_sqrt (le_of_lt (div_pos hm hR))
lemma circularSpeed_eq_rate {mu R : ℝ} (hm : 0 < mu) (hR : 0 < R) :
    R*circularRate mu R = circularSpeed mu R := by
  have ha := circularRate_sq hm hR
  have hb := circularSpeed_sq hm hR
  have hpos := mul_pos hR (circularRate_pos hm hR)
  have hpos' := circularSpeed_pos hm hR
  have hs : (R*circularRate mu R)^2 = circularSpeed mu R^2 := by
    rw [mul_pow, ha, hb]
    field_simp [ne_of_gt hR]
  nlinarith
lemma norm_circularPosition {mu R : ℝ} (hR : 0 < R) (phase t : ℝ) :
    ‖circularPosition mu R phase t‖ = R := by
  apply norm_pack_eq (le_of_lt hR)
  nlinarith [congrArg (fun x : ℝ => R^2*x)
    (Real.sin_sq_add_cos_sq (circularRate mu R*t+phase))]
lemma hasDerivAt_circularPosition (mu R phase t : ℝ) :
    HasDerivAt (circularPosition mu R phase) (circularVelocity mu R phase t) t := by
  have ha : HasDerivAt (fun s : ℝ => circularRate mu R*s+phase)
      (circularRate mu R) t := by
    simpa using ((hasDerivAt_id t).const_mul (circularRate mu R)).add_const phase
  convert pack_deriv (ha.cos.const_mul R) (ha.sin.const_mul R) using 1
  apply Complex.ext <;> simp [circularVelocity, pack] <;> ring
lemma hasDerivAt_circularVelocity (mu R phase t : ℝ) :
    HasDerivAt (circularVelocity mu R phase)
      (-(circularRate mu R)^2 • circularPosition mu R phase t) t := by
  have ha : HasDerivAt (fun s : ℝ => circularRate mu R*s+phase)
      (circularRate mu R) t := by
    simpa using ((hasDerivAt_id t).const_mul (circularRate mu R)).add_const phase
  convert pack_deriv (ha.sin.const_mul (-R*circularRate mu R))
    (ha.cos.const_mul (R*circularRate mu R)) using 1
  rw [circularPosition, pack_smul]
  apply Complex.ext <;> simp only [pack_re, pack_im] <;> ring
lemma circular_newton {mu R : ℝ} (hm : 0 < mu) (hR : 0 < R)
    (phase t : ℝ) :
    deriv (deriv (circularPosition mu R phase)) t =
      -(mu/‖circularPosition mu R phase t‖^3) • circularPosition mu R phase t := by
  have hv : deriv (circularPosition mu R phase) = circularVelocity mu R phase := by
    funext s; exact (hasDerivAt_circularPosition mu R phase s).deriv
  rw [hv, (hasDerivAt_circularVelocity mu R phase t).deriv,
    norm_circularPosition hR, circularRate_sq hm hR]

end HohmannTransfer
