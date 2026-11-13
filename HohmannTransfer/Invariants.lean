/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qianli Ma
-/
import HohmannTransfer.Dynamics

noncomputable section
namespace HohmannTransfer

/-! # Coast specific energy, angular momentum, and the vis-viva identity
These are computed from the position and its actual derivative, not defined
as the desired constant. Specific energy means energy per unit spacecraft mass.
-/
def specificEnergy (mu : ℝ) (q v : ℂ) : ℝ := ‖v‖^2/2 - mu/‖q‖

lemma velocity_numerator (p : Parameters) (u : ℝ) :
    p.a^2*Real.sin u^2 + p.b^2*Real.cos u^2 =
      p.a^2 * D p u * (1+p.e*Real.cos u) := by
  rw [p.b_sq_ellipse]
  have hsin : Real.sin u^2 = 1-Real.cos u^2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  rw [hsin]
  unfold D
  ring
lemma velocityAtAnomaly_norm_sq (p : Parameters) (u : ℝ) :
    ‖velocityAtAnomaly p u‖^2 =
      p.n^2*p.a^2*(1+p.e*Real.cos u)/D p u := by
  rw [← sqSpeed_eq_norm_sq]
  calc
    sqSpeed (velocityAtAnomaly p u) =
        p.n^2*(p.a^2*Real.sin u^2+p.b^2*Real.cos u^2)/(D p u)^2 := by
      unfold sqSpeed velocityAtAnomaly
      simp only [pack_re, pack_im]
      field_simp [D_ne p u]
      <;> ring
    _ = p.n^2*p.a^2*(1+p.e*Real.cos u)/D p u := by
      rw [velocity_numerator]
      field_simp [D_ne p u]
      <;> ring
lemma vis_viva_at_anomaly (p : Parameters) (u : ℝ) :
    ‖velocityAtAnomaly p u‖^2 = p.mu*(2/‖ellipse p u‖-1/p.a) := by
  rw [velocityAtAnomaly_norm_sq, norm_ellipse, p.n_sq]
  unfold radial
  field_simp [p.a_ne, D_ne p u]
  dsimp [D]
  ring
lemma vis_viva (p : Parameters) (t : ℝ) :
    ‖deriv (position p) t‖^2 = p.mu*(2/‖position p t‖-1/p.a) := by
  rw [deriv_position]
  exact vis_viva_at_anomaly p _
lemma coast_energy (p : Parameters) (t : ℝ) :
    specificEnergy p.mu (position p t) (deriv (position p) t) = -p.mu/(2*p.a) := by
  unfold specificEnergy
  rw [vis_viva]
  field_simp [p.a_ne, ne_of_gt (norm_position_pos p t)]
  <;> ring
lemma coast_energy_negative (p : Parameters) (t : ℝ) :
    specificEnergy p.mu (position p t) (deriv (position p) t) < 0 := by
  rw [coast_energy]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos p.mu_pos) (mul_pos (by norm_num) p.a_pos)
lemma angular_momentum_at_anomaly (p : Parameters) (u : ℝ) :
    cross (ellipse p u) (velocityAtAnomaly p u) = p.a*p.b*p.n := by
  have hs : Real.sin u^2 = 1-Real.cos u^2 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  unfold cross ellipse velocityAtAnomaly
  simp only [pack_re, pack_im]
  field_simp [D_ne p u]
  dsimp [D]
  nlinarith [congrArg (fun x : ℝ => p.a*p.b*p.n*x) hs]
lemma coast_angular_momentum (p : Parameters) (t : ℝ) :
    cross (position p t) (deriv (position p) t) = p.a*p.b*p.n := by
  rw [deriv_position]
  exact angular_momentum_at_anomaly p _
lemma coast_angular_momentum_pos (p : Parameters) (t : ℝ) :
    0 < cross (position p t) (deriv (position p) t) := by
  rw [coast_angular_momentum]
  exact mul_pos (mul_pos p.a_pos p.b_pos) p.n_pos

end HohmannTransfer
