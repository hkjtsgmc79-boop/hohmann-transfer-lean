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

/-! # A Euclidean plane, represented by ℂ
Distances always use the Euclidean complex norm, never the sup norm of a
coordinate-product type. `pack_deriv` transports two actual real derivatives.
-/
def pack (x y : ℝ) : ℂ := ⟨x, y⟩
def cross (z w : ℂ) : ℝ := z.re * w.im - z.im * w.re
def sqSpeed (z : ℂ) : ℝ := z.re ^ 2 + z.im ^ 2

@[simp] lemma pack_re (x y : ℝ) : (pack x y).re = x := rfl
@[simp] lemma pack_im (x y : ℝ) : (pack x y).im = y := rfl
lemma sqSpeed_eq_norm_sq (z : ℂ) : sqSpeed z = ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [sqSpeed, Complex.normSq_apply, pow_two]
lemma norm_pack_sq (x y : ℝ) : ‖pack x y‖ ^ 2 = x ^ 2 + y ^ 2 := by
  simpa [sqSpeed] using (sqSpeed_eq_norm_sq (pack x y)).symm
lemma norm_pack_eq {x y r : ℝ} (hr : 0 ≤ r) (hs : x^2+y^2=r^2) :
    ‖pack x y‖ = r := by
  have hn := norm_nonneg (pack x y)
  have h := norm_pack_sq x y
  nlinarith
lemma norm_pack_vertical (y : ℝ) : ‖pack 0 y‖ = |y| := by
  apply norm_pack_eq (abs_nonneg y)
  simp
lemma pack_deriv {f g : ℝ → ℝ} {f' g' t : ℝ}
    (hf : HasDerivAt f f' t) (hg : HasDerivAt g g' t) :
    HasDerivAt (fun s => pack (f s) (g s)) (pack f' g') t := by
  have hd := hf.ofReal_comp.add (hg.ofReal_comp.mul_const Complex.I)
  convert hd using 1
  · funext s
    apply Complex.ext <;> simp [pack]
  · apply Complex.ext <;> simp [pack]
lemma pack_smul (c x y : ℝ) : c • pack x y = pack (c*x) (c*y) := by
  apply Complex.ext <;> simp [pack]
lemma pack_sub (x y u v : ℝ) : pack x y - pack u v = pack (x-u) (y-v) := rfl
lemma pack_neg (x y : ℝ) : -pack x y = pack (-x) (-y) := rfl

end HohmannTransfer
