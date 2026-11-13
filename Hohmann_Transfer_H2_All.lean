/- Generated mechanically from the modular Hohmann sources. -/
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Norm

-- SOURCE MODULE: HohmannTransfer/Parameters.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

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

-- SOURCE MODULE: HohmannTransfer/Plane.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

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

-- SOURCE MODULE: HohmannTransfer/Geometry.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

noncomputable section
namespace HohmannTransfer

/-! # Eccentric-anomaly geometry, before introducing physical time
The attracting centre is the focus at 0, not the centre of the ellipse.
-/
def D (p : Parameters) (u : ℝ) : ℝ := 1 - p.e * Real.cos u
def radial (p : Parameters) (u : ℝ) : ℝ := p.a * D p u
def ellipse (p : Parameters) (u : ℝ) : ℂ :=
  pack (p.a * (Real.cos u - p.e)) (p.b * Real.sin u)
def velocityAtAnomaly (p : Parameters) (u : ℝ) : ℂ :=
  pack (-p.a * p.n * Real.sin u / D p u)
    (p.b * p.n * Real.cos u / D p u)

lemma D_lower (p : Parameters) (u : ℝ) : 1 - p.e ≤ D p u := by
  unfold D
  nlinarith [Real.cos_le_one u, p.e_pos]
lemma D_upper (p : Parameters) (u : ℝ) : D p u ≤ 1 + p.e := by
  unfold D
  nlinarith [Real.neg_one_le_cos u, p.e_pos]
lemma D_pos (p : Parameters) (u : ℝ) : 0 < D p u :=
  lt_of_lt_of_le p.one_sub_e_pos (D_lower p u)
lemma D_ne (p : Parameters) (u : ℝ) : D p u ≠ 0 := ne_of_gt (D_pos p u)
lemma radial_pos (p : Parameters) (u : ℝ) : 0 < radial p u :=
  mul_pos p.a_pos (D_pos p u)
lemma ellipse_squared_radius (p : Parameters) (u : ℝ) :
    (ellipse p u).re ^ 2 + (ellipse p u).im ^ 2 = (radial p u)^2 := by
  have hb := p.b_sq_ellipse
  have ht := Real.sin_sq_add_cos_sq u
  simp only [ellipse, pack_re, pack_im, radial, D]
  calc
    (p.a * (Real.cos u - p.e)) ^ 2 + (p.b * Real.sin u) ^ 2 =
        p.a^2*(Real.cos u-p.e)^2 + p.b^2*Real.sin u^2 := by ring
    _ = (p.a * (1-p.e*Real.cos u))^2 := by
      rw [hb]
      nlinarith [congrArg (fun x : ℝ => p.a^2*(1-p.e^2)*x) ht]
lemma norm_ellipse (p : Parameters) (u : ℝ) : ‖ellipse p u‖ = radial p u := by
  apply norm_pack_eq (le_of_lt (radial_pos p u))
  exact ellipse_squared_radius p u
lemma radial_bounds (p : Parameters) (u : ℝ) :
    p.r₁ ≤ radial p u ∧ radial p u ≤ p.r₂ := by
  constructor
  · rw [← p.a_mul_one_sub_e]
    exact mul_le_mul_of_nonneg_left (D_lower p u) (le_of_lt p.a_pos)
  · rw [← p.a_mul_one_add_e]
    exact mul_le_mul_of_nonneg_left (D_upper p u) (le_of_lt p.a_pos)
lemma ellipse_ne_zero (p : Parameters) (u : ℝ) : ellipse p u ≠ 0 := by
  intro h
  have hn := norm_ellipse p u
  rw [h, norm_zero] at hn
  linarith [radial_pos p u]
@[simp] lemma D_zero (p : Parameters) : D p 0 = 1 - p.e := by simp [D]
@[simp] lemma D_pi (p : Parameters) : D p Real.pi = 1 + p.e := by simp [D]
@[simp] lemma ellipse_zero (p : Parameters) : ellipse p 0 = pack p.r₁ 0 := by
  apply Complex.ext <;> simp [ellipse]
  exact p.a_mul_one_sub_e
@[simp] lemma ellipse_pi (p : Parameters) : ellipse p Real.pi = pack (-p.r₂) 0 := by
  apply Complex.ext <;> simp [ellipse]
  nlinarith [p.a_mul_one_add_e]
lemma ellipse_periodic (p : Parameters) : Function.Periodic (ellipse p) (2*Real.pi) := by
  intro u
  apply Complex.ext <;> simp [ellipse, Real.cos_add_two_pi, Real.sin_add_two_pi]

end HohmannTransfer

-- SOURCE MODULE: HohmannTransfer/KeplerClock.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

noncomputable section
namespace HohmannTransfer

/-! # Constructing physical time, not postulating a time parametrization
The clock K(u)=(u-e*sin u)/n is a strictly increasing bijection ℝ → ℝ.
Its inverse is constructed from that proof. Neither inverse existence nor its
ODE is a hypothesis of the public theorem.
-/
def clock (p : Parameters) (u : ℝ) : ℝ := (u - p.e * Real.sin u) / p.n

lemma hasDerivAt_clock (p : Parameters) (u : ℝ) :
    HasDerivAt (clock p) (D p u / p.n) u := by
  simpa [clock, D] using
    ((hasDerivAt_id u).sub ((Real.hasDerivAt_sin u).const_mul p.e)).div_const p.n
lemma clock_continuous (p : Parameters) : Continuous (clock p) := by
  exact continuous_iff_continuousAt.2 (fun u => (hasDerivAt_clock p u).continuousAt)
lemma clock_strictMono (p : Parameters) : StrictMono (clock p) := by
  apply strictMono_of_hasDerivAt_pos (hasDerivAt_clock p)
  intro u
  exact div_pos (D_pos p u) p.n_pos
lemma clock_bounds (p : Parameters) (u : ℝ) :
    (u-p.e)/p.n ≤ clock p u ∧ clock p u ≤ (u+p.e)/p.n := by
  constructor
  · apply (div_le_div_iff_of_pos_right p.n_pos).2
    nlinarith [p.e_pos, Real.sin_le_one u]
  · apply (div_le_div_iff_of_pos_right p.n_pos).2
    nlinarith [p.e_pos, Real.neg_one_le_sin u]
lemma clock_surjective (p : Parameters) : Function.Surjective (clock p) := by
  intro t
  apply mem_range_of_exists_le_of_exists_ge (clock_continuous p)
  · refine ⟨p.n*t-p.e, ?_⟩
    calc
      clock p (p.n*t-p.e) ≤ (p.n*t-p.e+p.e)/p.n := (clock_bounds p _).2
      _ = t := by field_simp [p.n_ne]; ring
  · refine ⟨p.n*t+p.e, ?_⟩
    calc
      t = (p.n*t+p.e-p.e)/p.n := by field_simp [p.n_ne]; ring
      _ ≤ clock p (p.n*t+p.e) := (clock_bounds p _).1

/-- The inverse is the inverse of a proved order isomorphism. -/
def clockIso (p : Parameters) : ℝ ≃o ℝ where
  toEquiv := Equiv.ofBijective (clock p)
    ⟨(clock_strictMono p).injective, clock_surjective p⟩
  map_rel_iff' := by
    intro x y
    exact (clock_strictMono p).le_iff_le

def anomaly (p : Parameters) (t : ℝ) : ℝ := (clockIso p).symm t

lemma clock_anomaly (p : Parameters) (t : ℝ) : clock p (anomaly p t) = t := by
  exact (clockIso p).apply_symm_apply t
lemma anomaly_clock (p : Parameters) (u : ℝ) : anomaly p (clock p u) = u := by
  exact (clockIso p).symm_apply_apply u
lemma anomaly_continuous (p : Parameters) : Continuous (anomaly p) :=
  (clockIso p).symm.continuous
lemma anomaly_strictMono (p : Parameters) : StrictMono (anomaly p) :=
  (clockIso p).symm.strictMono
lemma hasDerivAt_anomaly (p : Parameters) (t : ℝ) :
    HasDerivAt (anomaly p) (p.n / D p (anomaly p t)) t := by
  have h := HasDerivAt.of_local_left_inverse
    (anomaly_continuous p).continuousAt
    (hasDerivAt_clock p (anomaly p t))
    (ne_of_gt (div_pos (D_pos p _) p.n_pos))
    (Filter.Eventually.of_forall (clock_anomaly p))
  simpa only [inv_div] using h
@[simp] lemma clock_zero (p : Parameters) : clock p 0 = 0 := by simp [clock]
@[simp] lemma clock_pi (p : Parameters) : clock p Real.pi = p.transferTime := by
  simp [clock, Parameters.transferTime]
@[simp] lemma anomaly_zero (p : Parameters) : anomaly p 0 = 0 := by
  simpa using anomaly_clock p 0
@[simp] lemma anomaly_transferTime (p : Parameters) :
    anomaly p p.transferTime = Real.pi := by
  simpa using anomaly_clock p Real.pi
lemma kepler_equation (p : Parameters) (t : ℝ) :
    anomaly p t - p.e * Real.sin (anomaly p t) = p.n*t := by
  have h := clock_anomaly p t
  unfold clock at h
  exact ((div_eq_iff p.n_ne).mp h).trans (mul_comm t p.n)
lemma anomaly_bounds (p : Parameters) {t : ℝ} (ht : t ∈ Set.Icc 0 p.transferTime) :
    anomaly p t ∈ Set.Icc 0 Real.pi := by
  constructor
  · simpa using (anomaly_strictMono p).monotone ht.1
  · simpa using (anomaly_strictMono p).monotone ht.2
lemma clock_add_two_pi (p : Parameters) (u : ℝ) :
    clock p (u+2*Real.pi) = clock p u + 2*p.transferTime := by
  simp only [clock, Real.sin_add_two_pi, Parameters.transferTime]
  ring
lemma anomaly_add_period (p : Parameters) (t : ℝ) :
    anomaly p (t+2*p.transferTime) = anomaly p t + 2*Real.pi := by
  apply (clock_strictMono p).injective
  rw [clock_anomaly, clock_add_two_pi, clock_anomaly]

end HohmannTransfer

-- SOURCE MODULE: HohmannTransfer/Differentiation.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

noncomputable section
namespace HohmannTransfer

/-! # Actual first and second time derivatives
The eccentric anomaly is not linear in time except in the circular limit.
We differentiate the proved inverse Kepler clock, then apply the chain rule.
-/
def position (p : Parameters) (t : ℝ) : ℂ := ellipse p (anomaly p t)
def velocity (p : Parameters) (t : ℝ) : ℂ := velocityAtAnomaly p (anomaly p t)

lemma hasDerivAt_D (p : Parameters) (u : ℝ) :
    HasDerivAt (D p) (p.e*Real.sin u) u := by
  convert (hasDerivAt_const u (1:ℝ)).sub
    ((Real.hasDerivAt_cos u).const_mul p.e) using 1 <;> simp
lemma hasDerivAt_position (p : Parameters) (t : ℝ) :
    HasDerivAt (position p) (velocity p t) t := by
  have hu := hasDerivAt_anomaly p t
  have hx := (hu.cos.sub_const p.e).const_mul p.a
  have hy := hu.sin.const_mul p.b
  convert pack_deriv hx hy using 1
  apply Complex.ext <;>
    simp [velocity, velocityAtAnomaly, pack] <;> ring
lemma hasDerivAt_velocityAtAnomaly_x (p : Parameters) (u : ℝ) :
    HasDerivAt (fun s => (velocityAtAnomaly p s).re)
      (-p.a*p.n*(Real.cos u-p.e)/(D p u)^2) u := by
  have hnum := (Real.hasDerivAt_sin u).const_mul (-p.a*p.n)
  have h := hnum.div (hasDerivAt_D p u) (D_ne p u)
  convert h using 1
  apply (div_left_inj' (pow_ne_zero 2 (D_ne p u))).2
  unfold D
  nlinarith [congrArg (fun x : ℝ => p.a*p.n*p.e*x)
    (Real.sin_sq_add_cos_sq u)]
lemma hasDerivAt_velocityAtAnomaly_y (p : Parameters) (u : ℝ) :
    HasDerivAt (fun s => (velocityAtAnomaly p s).im)
      (-p.b*p.n*Real.sin u/(D p u)^2) u := by
  have hnum := (Real.hasDerivAt_cos u).const_mul (p.b*p.n)
  have h := hnum.div (hasDerivAt_D p u) (D_ne p u)
  convert h using 1
  apply (div_left_inj' (pow_ne_zero 2 (D_ne p u))).2
  unfold D
  ring
lemma hasDerivAt_velocity (p : Parameters) (t : ℝ) :
    HasDerivAt (velocity p)
      (-(p.n^2/(D p (anomaly p t))^3) • position p t) t := by
  have hx := (hasDerivAt_velocityAtAnomaly_x p (anomaly p t)).comp t
    (hasDerivAt_anomaly p t)
  have hy := (hasDerivAt_velocityAtAnomaly_y p (anomaly p t)).comp t
    (hasDerivAt_anomaly p t)
  convert pack_deriv hx hy using 1
  rw [position, ellipse, pack_smul]
  apply Complex.ext <;>
    simp only [pack_re, pack_im] <;>
    field_simp [D_ne p (anomaly p t)] <;> ring
lemma deriv_position (p : Parameters) : deriv (position p) = velocity p := by
  funext t
  exact (hasDerivAt_position p t).deriv
lemma position_continuous (p : Parameters) : Continuous (position p) :=
  continuous_iff_continuousAt.2 (fun t => (hasDerivAt_position p t).continuousAt)
lemma velocity_continuous (p : Parameters) : Continuous (velocity p) :=
  continuous_iff_continuousAt.2 (fun t => (hasDerivAt_velocity p t).continuousAt)

end HohmannTransfer

-- SOURCE MODULE: HohmannTransfer/Dynamics.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

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

-- SOURCE MODULE: HohmannTransfer/Circular.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

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

-- SOURCE MODULE: HohmannTransfer/Endpoints.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

noncomputable section
namespace HohmannTransfer

/-! # Endpoint geometry and speed derived from the actual time derivative -/
def periSpeed (p : Parameters) : ℝ := p.b*p.n/(1-p.e)
def apoSpeed (p : Parameters) : ℝ := p.b*p.n/(1+p.e)

lemma periSpeed_pos (p : Parameters) : 0 < periSpeed p :=
  div_pos (mul_pos p.b_pos p.n_pos) p.one_sub_e_pos
lemma apoSpeed_pos (p : Parameters) : 0 < apoSpeed p :=
  div_pos (mul_pos p.b_pos p.n_pos) p.one_add_e_pos
@[simp] lemma position_departure (p : Parameters) : position p 0 = pack p.r₁ 0 := by
  simp [position]
@[simp] lemma position_arrival (p : Parameters) :
    position p p.transferTime = pack (-p.r₂) 0 := by simp [position]
@[simp] lemma velocity_departure (p : Parameters) : velocity p 0 = pack 0 (periSpeed p) := by
  simp [velocity, velocityAtAnomaly, periSpeed]
@[simp] lemma velocity_arrival (p : Parameters) :
    velocity p p.transferTime = pack 0 (-apoSpeed p) := by
  apply Complex.ext <;> simp [velocity, velocityAtAnomaly, apoSpeed] <;> ring
lemma periSpeed_sq (p : Parameters) :
    periSpeed p ^ 2 = 2*p.mu*p.r₂/(p.r₁*(p.r₁+p.r₂)) := by
  have hper := p.a_mul_one_sub_e
  have haps := p.a_mul_one_add_e
  have hb := p.b_sq
  have hn := p.n_sq
  unfold periSpeed
  rw [div_pow, mul_pow, hb, hn]
  have he : 1-p.e = p.r₁/p.a := by
    apply (eq_div_iff p.a_ne).2
    nlinarith [hper]
  rw [he]
  unfold Parameters.a
  field_simp [p.r₁_ne, ne_of_gt p.sum_pos]

lemma apoSpeed_sq (p : Parameters) :
    apoSpeed p ^ 2 = 2*p.mu*p.r₁/(p.r₂*(p.r₁+p.r₂)) := by
  have haps := p.a_mul_one_add_e
  unfold apoSpeed
  rw [div_pow, mul_pow, p.b_sq, p.n_sq]
  have he : 1+p.e = p.r₂/p.a := by
    apply (eq_div_iff p.a_ne).2
    nlinarith [haps]
  rw [he]
  unfold Parameters.a
  field_simp [p.r₂_ne, ne_of_gt p.sum_pos]

lemma periSpeed_formula (p : Parameters) :
    periSpeed p = Real.sqrt (2*p.mu*p.r₂/(p.r₁*(p.r₁+p.r₂))) := by
  have hs := Real.sq_sqrt (le_of_lt
    (div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) p.mu_pos) p.r₂_pos) (mul_pos p.r₁_pos p.sum_pos)))
  have hn := Real.sqrt_nonneg (2*p.mu*p.r₂/(p.r₁*(p.r₁+p.r₂)))
  have hp := periSpeed_pos p
  have he := periSpeed_sq p
  nlinarith
lemma apoSpeed_formula (p : Parameters) :
    apoSpeed p = Real.sqrt (2*p.mu*p.r₁/(p.r₂*(p.r₁+p.r₂))) := by
  have hs := Real.sq_sqrt (le_of_lt
    (div_pos (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 2) p.mu_pos) p.r₁_pos) (mul_pos p.r₂_pos p.sum_pos)))
  have hn := Real.sqrt_nonneg (2*p.mu*p.r₁/(p.r₂*(p.r₁+p.r₂)))
  have hp := apoSpeed_pos p
  have he := apoSpeed_sq p
  nlinarith
lemma norm_velocity_departure (p : Parameters) : ‖velocity p 0‖ = periSpeed p := by
  rw [velocity_departure, norm_pack_vertical, abs_of_pos (periSpeed_pos p)]
lemma norm_velocity_arrival (p : Parameters) :
    ‖velocity p p.transferTime‖ = apoSpeed p := by
  rw [velocity_arrival, norm_pack_vertical, abs_neg, abs_of_pos (apoSpeed_pos p)]

end HohmannTransfer

-- SOURCE MODULE: HohmannTransfer/Impulses.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

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

-- SOURCE MODULE: HohmannTransfer/Invariants.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

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

-- SOURCE MODULE: HohmannTransfer/Transfer.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

noncomputable section
namespace HohmannTransfer

/-! # Joining the three coast arcs with two instantaneous impulses
All three arcs are defined on ℝ for easy differentiation; a flight uses the
incoming arc before 0, transfer arc on [0,τ], and outgoing arc after τ.
At the impulses position values match and velocity is allowed to jump.
No classical unforced ODE is asserted at either instantaneous burn.
-/
def incoming (p : Parameters) (t : ℝ) : ℂ := circularPosition p.mu p.r₁ 0 t
def outgoingPhase (p : Parameters) : ℝ := Real.pi-circularRate p.mu p.r₂*p.transferTime
def outgoing (p : Parameters) (t : ℝ) : ℂ :=
  circularPosition p.mu p.r₂ (outgoingPhase p) t
def flight (p : Parameters) (t : ℝ) : ℂ :=
  if t < 0 then incoming p t else if t ≤ p.transferTime then position p t else outgoing p t

lemma incoming_deriv (p : Parameters) (t : ℝ) :
    deriv (incoming p) t = circularVelocity p.mu p.r₁ 0 t :=
  (hasDerivAt_circularPosition _ _ _ _).deriv
lemma outgoing_deriv (p : Parameters) (t : ℝ) :
    deriv (outgoing p) t = circularVelocity p.mu p.r₂ (outgoingPhase p) t :=
  (hasDerivAt_circularPosition _ _ _ _).deriv
lemma incoming_newton (p : Parameters) (t : ℝ) :
    deriv (deriv (incoming p)) t = -(p.mu/‖incoming p t‖^3) • incoming p t :=
  circular_newton p.mu_pos p.r₁_pos 0 t
lemma outgoing_newton (p : Parameters) (t : ℝ) :
    deriv (deriv (outgoing p)) t = -(p.mu/‖outgoing p t‖^3) • outgoing p t :=
  circular_newton p.mu_pos p.r₂_pos (outgoingPhase p) t
lemma incoming_radius (p : Parameters) (t : ℝ) : ‖incoming p t‖ = p.r₁ :=
  norm_circularPosition p.r₁_pos 0 t
lemma outgoing_radius (p : Parameters) (t : ℝ) : ‖outgoing p t‖ = p.r₂ :=
  norm_circularPosition p.r₂_pos (outgoingPhase p) t
@[simp] lemma incoming_zero (p : Parameters) : incoming p 0 = pack p.r₁ 0 := by
  simp [incoming, circularPosition, pack]
lemma outgoing_angle (p : Parameters) :
    circularRate p.mu p.r₂*p.transferTime + outgoingPhase p = Real.pi := by
  unfold outgoingPhase
  ring
@[simp] lemma outgoing_arrival (p : Parameters) :
    outgoing p p.transferTime = pack (-p.r₂) 0 := by
  simp [outgoing, circularPosition, outgoing_angle, pack]
lemma incoming_velocity_zero (p : Parameters) :
    deriv (incoming p) 0 = pack 0 (circularSpeed p.mu p.r₁) := by
  rw [incoming_deriv]
  simp [circularVelocity, circularSpeed_eq_rate p.mu_pos p.r₁_pos, pack]
lemma outgoing_velocity_arrival (p : Parameters) :
    deriv (outgoing p) p.transferTime = pack 0 (-circularSpeed p.mu p.r₂) := by
  rw [outgoing_deriv]
  apply Complex.ext <;>
    simp [circularVelocity, outgoing_angle, pack, circularSpeed_eq_rate p.mu_pos p.r₂_pos]
lemma junction_positions (p : Parameters) :
    incoming p 0 = position p 0 ∧
      position p p.transferTime = outgoing p p.transferTime := by simp
lemma junction_velocity_jumps (p : Parameters) :
    deriv (position p) 0 - deriv (incoming p) 0 = entryImpulse p ∧
    deriv (outgoing p) p.transferTime - deriv (position p) p.transferTime = exitImpulse p := by
  rw [deriv_position, incoming_velocity_zero, outgoing_velocity_arrival]
  exact ⟨rfl,rfl⟩
lemma flight_before (p : Parameters) {t : ℝ} (ht : t < 0) :
    flight p t = incoming p t := by simp [flight, ht]
lemma flight_transfer (p : Parameters) {t : ℝ} (ht : t ∈ Set.Icc 0 p.transferTime) :
    flight p t = position p t := by simp [flight, not_lt.mpr ht.1, ht.2]
lemma flight_after (p : Parameters) {t : ℝ} (ht : p.transferTime < t) :
    flight p t = outgoing p t := by
  have h : ¬t<0 := not_lt.mpr (le_of_lt (lt_trans p.transferTime_pos ht))
  simp [flight, h, not_le.mpr ht]
lemma apsidal_parameters_unique (p : Parameters) {A E : ℝ}
    (hA : 0 < A) (h₁ : A*(1-E)=p.r₁) (h₂ : A*(1+E)=p.r₂) :
    A = p.a ∧ E = p.e := by
  have ha : A = p.a := by unfold Parameters.a; nlinarith
  refine ⟨ha, ?_⟩
  unfold Parameters.e
  apply (eq_div_iff (ne_of_gt p.sum_pos)).2
  have hsum : p.r₁ + p.r₂ = 2 * A := by linarith [h₁, h₂]
  rw [hsum]
  linarith [h₁, h₂]

end HohmannTransfer

-- SOURCE MODULE: HohmannTransfer/PublicStatement.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chengyuan AI Lab

H1 STATUS: uncompiled proof candidate; see STATUS.json.
-/

noncomputable section
namespace HohmannTransfer

/-! # Public theorem contract: outward Hohmann transfer
Fixed-centre, inverse-square, coplanar, circular-to-circular, two ideal impulses.
No claim of global fuel optimality, finite-thrust guidance, rendezvous with a
particular satellite, or existence for arbitrary initial velocities is made.
The public statements expose real derivatives and vector jump norms.
-/

theorem hohmann_transfer (p : Parameters) :
    0 < p.transferTime ∧
    (∀ t, deriv (deriv (position p)) t =
      -(p.mu/‖position p t‖^3) • position p t) ∧
    (∀ t, p.r₁ ≤ ‖position p t‖ ∧ ‖position p t‖ ≤ p.r₂) ∧
    position p 0 = pack p.r₁ 0 ∧
    position p p.transferTime = pack (-p.r₂) 0 ∧
    deriv (position p) 0 = pack 0 (periSpeed p) ∧
    deriv (position p) p.transferTime = pack 0 (-apoSpeed p) ∧
    incoming p 0 = position p 0 ∧
    position p p.transferTime = outgoing p p.transferTime ∧
    (∀ t, deriv (deriv (incoming p)) t =
      -(p.mu/‖incoming p t‖^3) • incoming p t) ∧
    (∀ t, deriv (deriv (outgoing p)) t =
      -(p.mu/‖outgoing p t‖^3) • outgoing p t) ∧
    ‖deriv (position p) 0-deriv (incoming p) 0‖ = deltaV₁ p ∧
    ‖deriv (outgoing p) p.transferTime-deriv (position p) p.transferTime‖ = deltaV₂ p ∧
    0 < deltaV₁ p ∧ 0 < deltaV₂ p ∧
    deltaV₁ p = Real.sqrt (p.mu/p.r₁)*(Real.sqrt (2*p.r₂/(p.r₁+p.r₂))-1) ∧
    deltaV₂ p = Real.sqrt (p.mu/p.r₂)*(1-Real.sqrt (2*p.r₁/(p.r₁+p.r₂))) ∧
    p.transferTime = Real.pi*Real.sqrt (p.a^3/p.mu) ∧
    (∀ t, specificEnergy p.mu (position p t) (deriv (position p) t) = -p.mu/(2*p.a)) ∧
    (∀ t, cross (position p t) (deriv (position p) t) = p.a*p.b*p.n) := by
  refine ⟨p.transferTime_pos, second_deriv_position p, position_bounds p,
    position_departure p, position_arrival p, ?_, ?_,
    (junction_positions p).1, (junction_positions p).2,
    incoming_newton p, outgoing_newton p, ?_, ?_,
    deltaV₁_pos p, deltaV₂_pos p, deltaV₁_formula p, deltaV₂_formula p,
    p.transferTime_eq, coast_energy p, coast_angular_momentum p⟩
  · rw [deriv_position, velocity_departure]
  · rw [deriv_position, velocity_arrival]
  · rw [(junction_velocity_jumps p).1, entryImpulse_norm]
  · rw [(junction_velocity_jumps p).2, exitImpulse_norm]

/-- Existence without asking the reader to trust a project-defined orbit predicate.
All geometric and motion hypotheses are consequences, not input fields. -/
theorem exists_hohmann_transfer (mu r₁ r₂ : ℝ)
    (hmu : 0 < mu) (hr₁ : 0 < r₁) (horder : r₁ < r₂) :
    ∃ (q v c₁ c₂ : ℝ → ℂ) (τ d₁ d₂ : ℝ),
      0 < τ ∧ 0 < d₁ ∧ 0 < d₂ ∧
      (∀ t, HasDerivAt q (v t) t) ∧
      (∀ t, HasDerivAt v (-(mu/‖q t‖^3) • q t) t) ∧
      (∀ t, deriv (deriv q) t = -(mu/‖q t‖^3) • q t) ∧
      (∀ t, r₁ ≤ ‖q t‖ ∧ ‖q t‖ ≤ r₂) ∧
      q 0 = pack r₁ 0 ∧ q τ = pack (-r₂) 0 ∧
      (∀ t, ‖c₁ t‖ = r₁) ∧ (∀ t, ‖c₂ t‖ = r₂) ∧
      (∀ t, deriv (deriv c₁) t = -(mu/‖c₁ t‖^3) • c₁ t) ∧
      (∀ t, deriv (deriv c₂) t = -(mu/‖c₂ t‖^3) • c₂ t) ∧
      c₁ 0 = q 0 ∧ q τ = c₂ τ ∧
      v 0-deriv c₁ 0 = pack 0 d₁ ∧
      deriv c₂ τ-v τ = pack 0 (-d₂) ∧
      ‖v 0-deriv c₁ 0‖ = d₁ ∧ ‖deriv c₂ τ-v τ‖ = d₂ ∧
      d₁ = Real.sqrt (mu/r₁)*(Real.sqrt (2*r₂/(r₁+r₂))-1) ∧
      d₂ = Real.sqrt (mu/r₂)*(1-Real.sqrt (2*r₁/(r₁+r₂))) ∧
      τ = Real.pi*Real.sqrt (((r₁+r₂)/2)^3/mu) := by
  let p : Parameters := ⟨mu,r₁,r₂,hmu,hr₁,horder⟩
  refine ⟨position p,velocity p,incoming p,outgoing p,
    p.transferTime,deltaV₁ p,deltaV₂ p,p.transferTime_pos,
    deltaV₁_pos p,deltaV₂_pos p,hasDerivAt_position p,
    hasDerivAt_velocity_newton p,second_deriv_position p,position_bounds p,
    position_departure p,position_arrival p,incoming_radius p,outgoing_radius p,
    incoming_newton p,outgoing_newton p,
    (junction_positions p).1,(junction_positions p).2,?_,?_,?_,?_,
    deltaV₁_formula p,deltaV₂_formula p,p.transferTime_eq⟩
  · rw [incoming_velocity_zero]
    exact entryImpulse_eq p
  · rw [outgoing_velocity_arrival]
    exact exitImpulse_eq p
  · rw [incoming_velocity_zero]
    exact entryImpulse_norm p
  · rw [outgoing_velocity_arrival]
    exact exitImpulse_norm p

end HohmannTransfer

-- SOURCE MODULE: HohmannOptimality/Shape.lean
/-
Copyright (c) 2026 Chengyuan AI Lab. Released under Apache 2.0.
H2: UNCOMPILED CANDIDATE. No kernel verification is claimed.
-/

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

-- SOURCE MODULE: HohmannOptimality/EndpointBounds.lean
/- H2 uncompiled candidate. Algebraic global bounds, with no calculus/KKT. -/

noncomputable section
namespace HohmannOptimality
open Shape

/-- Exact nonnegative certificate on the h ≤ hH half-plane. -/
lemma gap₁_low (s : Shape) (w h : ℝ) :
    s.burnSquare₁ w h - s.burnH₁ ^ 2 =
      (w + 2*s.alpha - s.alpha^2*h^2) +
      (s.hH-h)*(2-s.alpha^2*(h+s.hH)) := by
  dsimp [burnSquare₁, burnH₁]
  nlinarith [s.corner_relation]

lemma gap₁_high (s : Shape) (w h : ℝ) :
    s.burnSquare₁ w h - s.burnH₁ ^ 2 =
      (w+2-h^2) + (h-s.hH)*(h+s.hH-2) := by
  dsimp [burnSquare₁, burnH₁]
  ring

lemma gap₂_low (s : Shape) (w h : ℝ) :
    s.burnSquare₂ w h - s.burnH₂ ^ 2 =
      (w+2*s.alpha-s.alpha^2*h^2) +
      s.alpha*(s.hH-h)*(2*s.circularOuter-s.alpha*(h+s.hH)) := by
  dsimp [burnSquare₂, burnH₂]
  nlinarith [s.c_sq]

lemma gap₂_high (s : Shape) (w h : ℝ) :
    s.burnSquare₂ w h - s.burnH₂ ^ 2 =
      (w+2-h^2) + (h-s.hH)*(h+s.hH-2*s.alpha*s.circularOuter) := by
  dsimp [burnSquare₂, burnH₂]
  nlinarith [s.c_sq, s.corner_relation]

lemma low_factor₁_pos (s : Shape) {h : ℝ} (hh : h ≤ s.hH) :
    0 < 2 - s.alpha^2*(h+s.hH) := by
  have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg s.alpha)
  nlinarith [s.alpha_sq_h_lt_one]
lemma low_factor₂_pos (s : Shape) {h : ℝ} (hh : h ≤ s.hH) :
    0 < 2*s.circularOuter-s.alpha*(h+s.hH) := by
  have hm := mul_le_mul_of_nonneg_left hh (le_of_lt s.alpha_pos)
  nlinarith [s.alpha_h_lt_c]
lemma high_factor₁_pos (s : Shape) {h : ℝ} (hh : s.hH ≤ h) :
    0 < h+s.hH-2 := by linarith [s.one_lt_h]
lemma high_factor₂_pos (s : Shape) {h : ℝ} (hh : s.hH ≤ h) :
    0 < h+s.hH-2*s.alpha*s.circularOuter := by linarith [s.alpha_c_lt_h]

/-- Every feasible competitor pays at least the Hohmann first impulse. -/
theorem first_square_lower_bound (s : Shape) {w h : ℝ} (hf : s.Feasible w h) :
    s.burnH₁ ^ 2 ≤ s.burnSquare₁ w h := by
  by_cases hh : h ≤ s.hH
  · have hp := mul_nonneg (sub_nonneg.mpr hh) (le_of_lt (low_factor₁_pos s hh))
    have hs := sub_nonneg.mpr hf.2
    have hid := gap₁_low s w h
    linarith
  · have hh' : s.hH ≤ h := le_of_lt (lt_of_not_ge hh)
    have hp := mul_nonneg (sub_nonneg.mpr hh') (le_of_lt (high_factor₁_pos s hh'))
    have hs := sub_nonneg.mpr hf.1
    have hid := gap₁_high s w h
    linarith

/-- The second impulse separately also attains its global minimum at Hohmann. -/
theorem second_square_lower_bound (s : Shape) {w h : ℝ} (hf : s.Feasible w h) :
    s.burnH₂ ^ 2 ≤ s.burnSquare₂ w h := by
  by_cases hh : h ≤ s.hH
  · have hp := mul_nonneg
      (mul_nonneg (le_of_lt s.alpha_pos) (sub_nonneg.mpr hh))
      (le_of_lt (low_factor₂_pos s hh))
    have hs := sub_nonneg.mpr hf.2
    have hid := gap₂_low s w h
    linarith
  · have hh' : s.hH ≤ h := le_of_lt (lt_of_not_ge hh)
    have hp := mul_nonneg (sub_nonneg.mpr hh') (le_of_lt (high_factor₂_pos s hh'))
    have hs := sub_nonneg.mpr hf.1
    have hid := gap₂_high s w h
    linarith

lemma first_square_strict_of_h_ne (s : Shape) {w h : ℝ}
    (hf : s.Feasible w h) (hne : h ≠ s.hH) :
    s.burnH₁ ^ 2 < s.burnSquare₁ w h := by
  rcases lt_or_gt_of_ne hne with hh | hh
  · have hp := mul_pos (sub_pos.mpr hh) (low_factor₁_pos s (le_of_lt hh))
    have hid := gap₁_low s w h
    linarith [hf.2]
  · have hp := mul_pos (sub_pos.mpr hh) (high_factor₁_pos s (le_of_lt hh))
    have hid := gap₁_high s w h
    linarith [hf.1]

/-- The unique minimizer is an invariant pair, not a unique time-parametrized
trajectory: rotations and extra revolutions still have the same cost. -/
theorem invariant_pair_of_first_square_eq (s : Shape) {w h : ℝ}
    (hf : s.Feasible w h) (heq : s.burnSquare₁ w h = s.burnH₁^2) :
    h = s.hH ∧ w = s.energyH := by
  have hh : h = s.hH := by
    by_contra hn
    have hs := first_square_strict_of_h_ne s hf hn
    linarith
  refine ⟨hh, ?_⟩
  rw [hh] at heq
  dsimp [burnSquare₁, burnH₁, energyH] at *
  nlinarith

end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/EndpointOptimality.lean
/- H2 uncompiled candidate. Endpoints allow radial velocity and signed momentum. -/

noncomputable section
namespace HohmannOptimality
open Shape

/-- Two endpoint velocities in their own oriented radial/tangential frames.
The two conservation equalities are endpoint constraints, NOT a theorem that
arbitrary supplied data form a Kepler arc. Newton arcs are connected separately. -/
structure EndpointData (s : Shape) where
  radial₁ : ℝ
  tangent₁ : ℝ
  radial₂ : ℝ
  tangent₂ : ℝ
  angular : tangent₂ = s.alpha * tangent₁
  energy : radial₁^2+tangent₁^2-2 = radial₂^2+tangent₂^2-2*s.alpha

namespace EndpointData

def w {s : Shape} (z : EndpointData s) : ℝ := z.radial₁^2+z.tangent₁^2-2
def impulse₁ {s : Shape} (z : EndpointData s) : ℝ :=
  Real.sqrt (z.radial₁^2+(z.tangent₁-1)^2)
def impulse₂ {s : Shape} (z : EndpointData s) : ℝ :=
  Real.sqrt (z.radial₂^2+(z.tangent₂-s.circularOuter)^2)
def cost {s : Shape} (z : EndpointData s) : ℝ := z.impulse₁ + z.impulse₂

lemma feasible {s : Shape} (z : EndpointData s) : s.Feasible z.w z.tangent₁ := by
  constructor
  · dsimp [w]; nlinarith [sq_nonneg z.radial₁]
  · have he := z.energy
    rw [z.angular] at he
    dsimp [w]
    nlinarith [sq_nonneg z.radial₂]
lemma impulse₁_nonneg {s : Shape} (z : EndpointData s) : 0 ≤ z.impulse₁ :=
  Real.sqrt_nonneg _
lemma impulse₂_nonneg {s : Shape} (z : EndpointData s) : 0 ≤ z.impulse₂ :=
  Real.sqrt_nonneg _
lemma impulse₁_sq {s : Shape} (z : EndpointData s) :
    z.impulse₁^2 = z.radial₁^2+(z.tangent₁-1)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma impulse₂_sq {s : Shape} (z : EndpointData s) :
    z.impulse₂^2 = z.radial₂^2+(z.tangent₂-s.circularOuter)^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma impulse₁_sq_invariant {s : Shape} (z : EndpointData s) :
    z.impulse₁^2 = s.burnSquare₁ z.w z.tangent₁ := by
  rw [z.impulse₁_sq]
  dsimp [w, burnSquare₁]
  ring
lemma impulse₂_sq_invariant {s : Shape} (z : EndpointData s) :
    z.impulse₂^2 = s.burnSquare₂ z.w z.tangent₁ := by
  rw [z.impulse₂_sq, z.angular]
  have he := z.energy
  rw [z.angular] at he
  dsimp [w, burnSquare₂]
  nlinarith [s.c_sq]

end EndpointData

/-- A global inequality over ALL feasible endpoint velocities, not merely a
stationary-point or small-perturbation calculation. -/
theorem endpoint_impulses_lower_bound (s : Shape) (z : EndpointData s) :
    s.burnH₁ ≤ z.impulse₁ ∧ s.burnH₂ ≤ z.impulse₂ := by
  have h₁ := first_square_lower_bound s z.feasible
  have h₂ := second_square_lower_bound s z.feasible
  rw [← z.impulse₁_sq_invariant] at h₁
  rw [← z.impulse₂_sq_invariant] at h₂
  constructor
  · nlinarith [s.burnH₁_pos, z.impulse₁_nonneg]
  · nlinarith [s.burnH₂_pos, z.impulse₂_nonneg]

theorem endpoint_total_lower_bound (s : Shape) (z : EndpointData s) :
    s.costH ≤ z.cost := by
  have h := endpoint_impulses_lower_bound s z
  exact add_le_add h.1 h.2

/-- A feasible corner achieving the lower bound; physical attainment is H1. -/
def hohmannEndpoints (s : Shape) : EndpointData s where
  radial₁ := 0
  tangent₁ := s.hH
  radial₂ := 0
  tangent₂ := s.alpha*s.hH
  angular := rfl
  energy := by nlinarith [s.corner_relation]

lemma hohmannEndpoints_cost (s : Shape) : (hohmannEndpoints s).cost = s.costH := by
  have h₁ : (hohmannEndpoints s).impulse₁ = s.burnH₁ := by
    have hs := (hohmannEndpoints s).impulse₁_sq
    have hn := (hohmannEndpoints s).impulse₁_nonneg
    dsimp [hohmannEndpoints, burnH₁] at *
    nlinarith [s.one_lt_h]
  have h₂ : (hohmannEndpoints s).impulse₂ = s.burnH₂ := by
    have hs := (hohmannEndpoints s).impulse₂_sq
    have hn := (hohmannEndpoints s).impulse₂_nonneg
    dsimp [hohmannEndpoints, burnH₂] at *
    nlinarith [s.alpha_h_lt_c]
  exact congrArg₂ (· + ·) h₁ h₂

/-- Equality forces both endpoint radial velocities to vanish and fixes signed
angular momentum. No claim of uniqueness of flight time or orientation. -/
theorem endpoint_equality_characterization (s : Shape) (z : EndpointData s)
    (heq : z.cost = s.costH) :
    z.tangent₁ = s.hH ∧ z.tangent₂ = s.alpha*s.hH ∧
      z.radial₁ = 0 ∧ z.radial₂ = 0 := by
  have hb := endpoint_impulses_lower_bound s z
  have he₁ : z.impulse₁ = s.burnH₁ := by
    dsimp [EndpointData.cost, costH] at heq
    linarith
  have hs : s.burnSquare₁ z.w z.tangent₁ = s.burnH₁^2 := by
    rw [← z.impulse₁_sq_invariant, he₁]
  have pair := invariant_pair_of_first_square_eq s z.feasible hs
  have htan₂ : z.tangent₂ = s.alpha*s.hH := by rw [z.angular, pair.1]
  have hu : z.radial₁=0 := by
    have hw := pair.2
    dsimp [EndpointData.w, energyH] at hw
    rw [pair.1] at hw
    nlinarith [sq_nonneg z.radial₁]
  have hv : z.radial₂=0 := by
    have he := z.energy
    rw [hu, pair.1, htan₂] at he
    nlinarith [s.corner_relation, sq_nonneg z.radial₂]
  exact ⟨pair.1, htan₂, hu, hv⟩

end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/PhysicalUnits.lean
/- H2 uncompiled candidate. Restore arbitrary positive μ and length scale. -/

noncomputable section
namespace HohmannOptimality

structure Units where
  mu : ℝ
  r₁ : ℝ
  r₂ : ℝ
  mu_pos : 0 < mu
  r₁_pos : 0 < r₁
  outward : r₁ < r₂

namespace Units

lemma r₂_pos (p : Units) : 0 < p.r₂ := lt_trans p.r₁_pos p.outward
lemma r₁_ne (p : Units) : p.r₁ ≠ 0 := ne_of_gt p.r₁_pos
lemma r₂_ne (p : Units) : p.r₂ ≠ 0 := ne_of_gt p.r₂_pos

def shape (p : Units) : Shape where
  alpha := p.r₁/p.r₂
  alpha_pos := div_pos p.r₁_pos p.r₂_pos
  alpha_lt_one := (div_lt_one p.r₂_pos).2 p.outward

def speed (p : Units) : ℝ := Real.sqrt (p.mu/p.r₁)
def circular₂ (p : Units) : ℝ := p.speed*p.shape.circularOuter
def bound (p : Units) : ℝ := p.speed*p.shape.costH

lemma speed_pos (p : Units) : 0 < p.speed := Real.sqrt_pos.2 (div_pos p.mu_pos p.r₁_pos)
lemma speed_ne (p : Units) : p.speed ≠ 0 := ne_of_gt p.speed_pos
lemma speed_sq (p : Units) : p.speed^2 = p.mu/p.r₁ :=
  Real.sq_sqrt (le_of_lt (div_pos p.mu_pos p.r₁_pos))
lemma mu_over_r₂ (p : Units) : p.mu/p.r₂ = p.shape.alpha*p.speed^2 := by
  rw [p.speed_sq]
  dsimp [shape]
  field_simp [p.r₁_ne, p.r₂_ne]

lemma circular₂_eq_sqrt (p : Units) : p.circular₂ = Real.sqrt (p.mu/p.r₂) := by
  have hs : p.circular₂^2 = p.mu/p.r₂ := by
    dsimp [circular₂]
    rw [mul_pow, p.shape.c_sq, p.mu_over_r₂]
    ring
  have hn := mul_pos p.speed_pos p.shape.c_pos
  have hq := Real.sq_sqrt (le_of_lt (div_pos p.mu_pos p.r₂_pos))
  have hr := Real.sqrt_nonneg (p.mu/p.r₂)
  dsimp [circular₂] at *
  nlinarith

end Units

structure PhysicalEndpoints (p : Units) where
  radial₁ : ℝ
  tangent₁ : ℝ
  radial₂ : ℝ
  tangent₂ : ℝ
  angular : p.r₁*tangent₁ = p.r₂*tangent₂
  energy : radial₁^2+tangent₁^2-2*p.mu/p.r₁ =
    radial₂^2+tangent₂^2-2*p.mu/p.r₂

namespace PhysicalEndpoints

def cost {p : Units} (z : PhysicalEndpoints p) : ℝ :=
  Real.sqrt (z.radial₁^2+(z.tangent₁-p.speed)^2) +
  Real.sqrt (z.radial₂^2+(z.tangent₂-p.circular₂)^2)

def normalized {p : Units} (z : PhysicalEndpoints p) : EndpointData p.shape where
  radial₁ := z.radial₁/p.speed
  tangent₁ := z.tangent₁/p.speed
  radial₂ := z.radial₂/p.speed
  tangent₂ := z.tangent₂/p.speed
  angular := by
    change z.tangent₂/p.speed = (p.r₁/p.r₂)*(z.tangent₁/p.speed)
    field_simp [p.speed_ne, p.r₂_ne]
    nlinarith [z.angular]
  energy := by
    have he := z.energy
    have he' : z.radial₁^2+z.tangent₁^2-2*p.speed^2 =
        z.radial₂^2+z.tangent₂^2-2*p.shape.alpha*p.speed^2 := by
      calc
        _ = z.radial₁^2+z.tangent₁^2-2*p.mu/p.r₁ := by rw [p.speed_sq]; ring
        _ = z.radial₂^2+z.tangent₂^2-2*p.mu/p.r₂ := he
        _ = _ := by rw [show 2*p.mu/p.r₂=2*(p.mu/p.r₂) by ring, p.mu_over_r₂]; ring
    field_simp [p.speed_ne]
    nlinarith [he']

lemma norm_scale (a b v : ℝ) (hv : 0 < v) :
    v*Real.sqrt ((a/v)^2+(b/v)^2) = Real.sqrt (a^2+b^2) := by
  have h₁ := Real.sq_sqrt (add_nonneg (sq_nonneg (a/v)) (sq_nonneg (b/v)))
  have h₂ := Real.sq_sqrt (add_nonneg (sq_nonneg a) (sq_nonneg b))
  have hs : (v*Real.sqrt ((a/v)^2+(b/v)^2))^2 = a^2+b^2 := by
    rw [mul_pow, h₁]
    field_simp [ne_of_gt hv]

  have hn := mul_nonneg (le_of_lt hv) (Real.sqrt_nonneg ((a/v)^2+(b/v)^2))
  nlinarith [Real.sqrt_nonneg (a^2+b^2)]

lemma cost_eq_scaled {p : Units} (z : PhysicalEndpoints p) :
    z.cost = p.speed*z.normalized.cost := by
  dsimp [cost, normalized, EndpointData.cost, EndpointData.impulse₁, EndpointData.impulse₂]
  rw [mul_add]
  have h₁ : z.tangent₁/p.speed-1=(z.tangent₁-p.speed)/p.speed := by
    field_simp [p.speed_ne]
  have h₂ : z.tangent₂/p.speed-p.shape.circularOuter =
      (z.tangent₂-p.circular₂)/p.speed := by
    dsimp [Units.circular₂]
    field_simp [p.speed_ne]
  rw [h₁, h₂, norm_scale _ _ _ p.speed_pos, norm_scale _ _ _ p.speed_pos]

theorem physical_lower_bound {p : Units} (z : PhysicalEndpoints p) : p.bound ≤ z.cost := by
  rw [z.cost_eq_scaled]
  exact mul_le_mul_of_nonneg_left (endpoint_total_lower_bound p.shape z.normalized)
    (le_of_lt p.speed_pos)

end PhysicalEndpoints
end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/PlanarState.lean
/- H2 uncompiled candidate. Euclidean, NOT a product-type sup-norm. -/

noncomputable section
namespace HohmannOptimality

structure PlanarState where
  x : ℝ
  y : ℝ
  vx : ℝ
  vy : ℝ

namespace PlanarState

def radius (z : PlanarState) : ℝ := Real.sqrt (z.x^2+z.y^2)
def angular (z : PlanarState) : ℝ := z.x*z.vy-z.y*z.vx
def radial (z : PlanarState) : ℝ := (z.x*z.vx+z.y*z.vy)/z.radius
def tangent (z : PlanarState) : ℝ := z.angular/z.radius
def energy (z : PlanarState) (mu : ℝ) : ℝ := z.vx^2+z.vy^2-2*mu/z.radius
/-- Actual Cartesian speed change to/from the same prograde circular velocity. -/
def impulse (z : PlanarState) (c : ℝ) : ℝ :=
  Real.sqrt ((z.vx+c*z.y/z.radius)^2+(z.vy-c*z.x/z.radius)^2)

lemma radius_sq (z : PlanarState) : z.radius^2=z.x^2+z.y^2 :=
  Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
lemma radius_mul_tangent (z : PlanarState) (hr : 0 < z.radius) :
    z.radius*z.tangent = z.angular := by
  dsimp [tangent]
  field_simp [ne_of_gt hr]
lemma polar_speed_sq (z : PlanarState) (hr : 0 < z.radius) :
    z.radial^2+z.tangent^2=z.vx^2+z.vy^2 := by
  have hi : (z.x*z.vx+z.y*z.vy)^2+(z.x*z.vy-z.y*z.vx)^2 =
      (z.x^2+z.y^2)*(z.vx^2+z.vy^2) := by ring
  dsimp [radial, tangent, angular]
  field_simp [ne_of_gt hr]
  nlinarith [congrArg (fun u : ℝ => u*(z.vx^2+z.vy^2)) z.radius_sq]
lemma impulse_polar (z : PlanarState) (c : ℝ) (hr : 0 < z.radius) :
    z.impulse c = Real.sqrt (z.radial^2+(z.tangent-c)^2) := by
  unfold impulse
  congr 1
  dsimp [radial, tangent, angular]
  field_simp [ne_of_gt hr]
  nlinarith [congrArg (fun u : ℝ => u*(z.vx^2+z.vy^2-c^2)) z.radius_sq]

end PlanarState
end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/KeplerConservation.lean
/- H2 uncompiled candidate. Conservation is DERIVED from genuine derivatives.
Only the smooth coast interval is modeled; impulses are endpoint velocity jumps.
-/

noncomputable section
namespace HohmannOptimality
open Set

structure KeplerArc (mu : ℝ) where
  t₀ : ℝ
  t₁ : ℝ
  time_order : t₀ < t₁
  x : ℝ → ℝ
  y : ℝ → ℝ
  vx : ℝ → ℝ
  vy : ℝ → ℝ
  radius_pos : ∀ t ∈ Icc t₀ t₁, 0 < Real.sqrt (x t^2+y t^2)
  dx : ∀ t ∈ Icc t₀ t₁, HasDerivAt x (vx t) t
  dy : ∀ t ∈ Icc t₀ t₁, HasDerivAt y (vy t) t
  dvx : ∀ t ∈ Icc t₀ t₁,
    HasDerivAt vx (-mu*x t/(Real.sqrt (x t^2+y t^2))^3) t
  dvy : ∀ t ∈ Icc t₀ t₁,
    HasDerivAt vy (-mu*y t/(Real.sqrt (x t^2+y t^2))^3) t

namespace KeplerArc

def state {mu : ℝ} (a : KeplerArc mu) (t : ℝ) : PlanarState :=
  ⟨a.x t,a.y t,a.vx t,a.vy t⟩
lemma left_mem {mu : ℝ} (a : KeplerArc mu) : a.t₀ ∈ Icc a.t₀ a.t₁ :=
  ⟨le_rfl, le_of_lt a.time_order⟩
lemma right_mem {mu : ℝ} (a : KeplerArc mu) : a.t₁ ∈ Icc a.t₀ a.t₁ :=
  ⟨le_of_lt a.time_order, le_rfl⟩

lemma radius_deriv {mu t : ℝ} (a : KeplerArc mu) (ht : t ∈ Icc a.t₀ a.t₁) :
    HasDerivAt (fun u => (a.state u).radius)
      ((a.x t*a.vx t+a.y t*a.vy t)/(a.state t).radius) t := by
  have hr := a.radius_pos t ht
  have harg : a.x t^2+a.y t^2 ≠ 0 := by
    intro hz
    rw [hz, Real.sqrt_zero] at hr
    exact (lt_irrefl 0) hr
  have hd := (((a.dx t ht).pow 2).add ((a.dy t ht).pow 2)).sqrt harg
  convert hd using 1
  dsimp [state, PlanarState.radius]
  field_simp [ne_of_gt hr]

lemma angular_deriv_zero {mu t : ℝ} (a : KeplerArc mu) (ht : t ∈ Icc a.t₀ a.t₁) :
    HasDerivAt (fun u => (a.state u).angular) 0 t := by
  have hd := ((a.dx t ht).mul (a.dvy t ht)).sub ((a.dy t ht).mul (a.dvx t ht))
  convert hd using 1
  field_simp [ne_of_gt (a.radius_pos t ht)]
  ring

lemma energy_deriv_zero {mu t : ℝ} (a : KeplerArc mu) (ht : t ∈ Icc a.t₀ a.t₁) :
    HasDerivAt (fun u => (a.state u).energy mu) 0 t := by
  have hr : (a.state t).radius ≠ 0 := ne_of_gt (a.radius_pos t ht)
  have hk := ((a.dvx t ht).pow 2).add ((a.dvy t ht).pow 2)
  have hp := (hasDerivAt_const t (2*mu)).div (a.radius_deriv ht) hr
  convert hk.sub hp using 1
  dsimp [state, PlanarState.radius] at hr ⊢
  field_simp [hr]
  ring

lemma equal_endpoints_of_zero_deriv {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hd : ∀ t ∈ Icc a b, HasDerivAt f 0 t) : f b=f a := by
  have hc : ContinuousOn f (Icc a b) := by
    intro t ht
    exact (hd t ht).continuousAt.continuousWithinAt
  have hh : ∀ t ∈ Ico a b, HasDerivWithinAt f 0 (Ici t) t := by
    intro t ht
    exact (hd t ⟨ht.1, le_of_lt ht.2⟩).hasDerivWithinAt
  exact constant_of_has_deriv_right_zero hc hh b ⟨hab,le_rfl⟩

theorem energy_conserved {mu : ℝ} (a : KeplerArc mu) :
    (a.state a.t₀).energy mu = (a.state a.t₁).energy mu := by
  exact (equal_endpoints_of_zero_deriv (le_of_lt a.time_order)
    (fun _ ht => a.energy_deriv_zero ht)).symm

theorem angular_conserved {mu : ℝ} (a : KeplerArc mu) :
    (a.state a.t₀).angular = (a.state a.t₁).angular := by
  exact (equal_endpoints_of_zero_deriv (le_of_lt a.time_order)
    (fun _ ht => a.angular_deriv_zero ht)).symm

/-- Obtain endpoint constraints from the actual ODE; no conservation law is an
input field of KeplerArc. Endpoint orientation and coast time are unrestricted. -/
def endpoints (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂) :
    PhysicalEndpoints p where
  radial₁ := (a.state a.t₀).radial
  tangent₁ := (a.state a.t₀).tangent
  radial₂ := (a.state a.t₁).radial
  tangent₂ := (a.state a.t₁).tangent
  angular := by
    rw [← h₀, ← h₁, PlanarState.radius_mul_tangent (a.state a.t₀) (a.radius_pos _ a.left_mem),
      PlanarState.radius_mul_tangent (a.state a.t₁) (a.radius_pos _ a.right_mem)]
    exact a.angular_conserved
  energy := by
    rw [PlanarState.polar_speed_sq (a.state a.t₀) (a.radius_pos _ a.left_mem),
      PlanarState.polar_speed_sq (a.state a.t₁) (a.radius_pos _ a.right_mem), ← h₀, ← h₁]
    exact a.energy_conserved

/-- Global two-impulse lower bound for every noncollision Newtonian coast arc.
No tangency, ellipse, energy sign or positive angular momentum is assumed. -/
theorem newton_arc_lower_bound (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius=p.r₁) (h₁ : (a.state a.t₁).radius=p.r₂) :
    p.bound ≤ (a.state a.t₀).impulse p.speed + (a.state a.t₁).impulse p.circular₂ := by
  rw [PlanarState.impulse_polar (a.state a.t₀) _ (a.radius_pos _ a.left_mem),
    PlanarState.impulse_polar (a.state a.t₁) _ (a.radius_pos _ a.right_mem)]
  exact (endpoints p a h₀ h₁).physical_lower_bound

/-- Equality of the actual Cartesian cost forces the Hohmann endpoint velocities. -/
theorem newton_arc_equality_endpoints (p : Units) (a : KeplerArc p.mu)
    (h₀ : (a.state a.t₀).radius = p.r₁) (h₁ : (a.state a.t₁).radius = p.r₂)
    (he : (a.state a.t₀).impulse p.speed + (a.state a.t₁).impulse p.circular₂ = p.bound) :
    (a.state a.t₀).radial = 0 ∧ (a.state a.t₁).radial = 0 ∧
    (a.state a.t₀).tangent = p.speed * p.shape.hH ∧
    (a.state a.t₁).tangent = p.speed * (p.shape.alpha * p.shape.hH) := by
  let z := endpoints p a h₀ h₁
  rw [PlanarState.impulse_polar (a.state a.t₀) _ (a.radius_pos _ a.left_mem),
    PlanarState.impulse_polar (a.state a.t₁) _ (a.radius_pos _ a.right_mem)] at he
  change z.cost = p.speed * p.shape.costH at he
  rw [z.cost_eq_scaled] at he
  have hnorm := mul_left_cancel₀ p.speed_ne he
  obtain ⟨ht₁, ht₂, hu₁, hu₂⟩ := endpoint_equality_characterization p.shape z.normalized hnorm
  change (a.state a.t₀).tangent / p.speed = p.shape.hH at ht₁
  change (a.state a.t₁).tangent / p.speed = p.shape.alpha * p.shape.hH at ht₂
  change (a.state a.t₀).radial / p.speed = 0 at hu₁
  change (a.state a.t₁).radial / p.speed = 0 at hu₂
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [zero_mul] using (div_eq_iff p.speed_ne).1 hu₁
  · simpa only [zero_mul] using (div_eq_iff p.speed_ne).1 hu₂
  · exact ((div_eq_iff p.speed_ne).1 ht₁).trans (mul_comm _ _)
  · exact ((div_eq_iff p.speed_ne).1 ht₂).trans (mul_comm _ _)

end KeplerArc
end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/Bielliptic.lean
/- H2 uncompiled candidate. A finite three-burn competitor, not an infinite limit. -/

noncomputable section
namespace HohmannOptimality
namespace Bielliptic

/-- Normalized radii: departure 1, target R, common apocentre B. -/
structure Parameters where
  R : ℝ
  B : ℝ
  one_lt_R : 1 < R
  R_lt_B : R < B

/-- First ellipse periapsis speed. -/
def departureSpeed (p : Parameters) : ℝ := Real.sqrt (2*p.B/(1+p.B))
/-- Second ellipse periapsis speed at the final radius. -/
def arrivalSpeed (p : Parameters) : ℝ := Real.sqrt (2*p.B/(p.R*(p.R+p.B)))
def firstApoSpeed (p : Parameters) : ℝ := departureSpeed p / p.B
def secondApoSpeed (p : Parameters) : ℝ := p.R*arrivalSpeed p / p.B
/-- Three actual speed-jump magnitudes; the final burn is retrograde. -/
def cost (p : Parameters) : ℝ :=
  |departureSpeed p - 1| + |secondApoSpeed p - firstApoSpeed p| +
  |arrivalSpeed p - 1/Real.sqrt p.R|

def hohmannPeri (R : ℝ) : ℝ := Real.sqrt (2*R/(1+R))
def hohmannCost (R : ℝ) : ℝ :=
  |hohmannPeri R-1| + |1/Real.sqrt R-hohmannPeri R/R|

def time (p : Parameters) : ℝ :=
  Real.pi*(Real.sqrt (((1+p.B)/2)^3)+Real.sqrt (((p.R+p.B)/2)^3))
def hohmannTime (R : ℝ) : ℝ := Real.pi*Real.sqrt (((1+R)/2)^3)

lemma cost_nonneg (p : Parameters) : 0 ≤ cost p := by
  unfold cost
  positivity
lemma time_pos (p : Parameters) : 0 < time p := by
  have hR : 0 < p.R := lt_trans (by norm_num) p.one_lt_R
  have hB : 0 < p.B := lt_trans hR p.R_lt_B
  unfold time
  positivity

/-- Concrete finite-radius witness. -/
def «example» : Parameters := ⟨16,64,by norm_num,by norm_num⟩

lemma example_departure : departureSpeed «example» = Real.sqrt (128/65 : ℝ) := by
  norm_num [departureSpeed, «example»]
lemma example_arrival : arrivalSpeed «example» = Real.sqrt (1/10 : ℝ) := by
  norm_num [arrivalSpeed, «example»]
lemma example_hohmann : hohmannPeri 16 = Real.sqrt (32/17 : ℝ) := by
  norm_num [hohmannPeri]

/-- Rational squared bounds; no floating-point/native evaluation is involved. -/
lemma sqrt_rational_interval {x l u : ℝ} (hl : 0 ≤ l) (hu : 0 ≤ u)
    (hlo : l^2 ≤ x) (hhi : x ≤ u^2) : l ≤ Real.sqrt x ∧ Real.sqrt x ≤ u := by
  have hx : 0 ≤ x := le_trans (sq_nonneg l) hlo
  have hs := Real.sq_sqrt hx
  have hn := Real.sqrt_nonneg x
  constructor <;> nlinarith

lemma example_root_H_bounds :
    (13719/10000 : ℝ) ≤ Real.sqrt (32/17 : ℝ) ∧
      Real.sqrt (32/17 : ℝ) ≤ (1372/1000 : ℝ) := by
  apply sqrt_rational_interval <;> norm_num
lemma example_root_A_bounds :
    (7/5 : ℝ) ≤ Real.sqrt (128/65 : ℝ) ∧
      Real.sqrt (128/65 : ℝ) ≤ (14033/10000 : ℝ) := by
  apply sqrt_rational_interval <;> norm_num
lemma example_root_D_bounds :
    (31/100 : ℝ) ≤ Real.sqrt (1/10 : ℝ) ∧
      Real.sqrt (1/10 : ℝ) ≤ (31623/100000 : ℝ) := by
  apply sqrt_rational_interval <;> norm_num

lemma example_cost_closed : cost «example» =
    (63/64 : ℝ)*Real.sqrt (128/65 : ℝ) +
      (5/4 : ℝ)*Real.sqrt (1/10 : ℝ) - (5/4 : ℝ) := by
  have hA := example_root_A_bounds
  have hD := example_root_D_bounds
  have h₁ : 0 ≤ Real.sqrt (128/65 : ℝ)-1 := by linarith
  have h₂ : 0 ≤ Real.sqrt (1/10 : ℝ)/4-Real.sqrt (128/65 : ℝ)/64 := by linarith
  have h₃ : 0 ≤ Real.sqrt (1/10 : ℝ)-(1/4 : ℝ) := by linarith
  unfold cost firstApoSpeed secondApoSpeed
  rw [example_departure, example_arrival]
  change |Real.sqrt (128/65 : ℝ)-1| +
    |16*Real.sqrt (1/10 : ℝ)/64-Real.sqrt (128/65 : ℝ)/64| +
    |Real.sqrt (1/10 : ℝ)-1/Real.sqrt 16| = _
  rw [show Real.sqrt (16 : ℝ) = 4 by norm_num]
  rw [show 16*Real.sqrt (1/10 : ℝ)/64=Real.sqrt (1/10 : ℝ)/4 by ring,
    abs_of_nonneg h₁, abs_of_nonneg h₂, abs_of_nonneg h₃]
  ring

lemma example_hohmann_closed : hohmannCost 16 =
    (15/16 : ℝ)*Real.sqrt (32/17 : ℝ)-(3/4 : ℝ) := by
  have hH := example_root_H_bounds
  have h₁ : 0 ≤ Real.sqrt (32/17 : ℝ)-1 := by linarith
  have h₂ : 0 ≤ (1/4 : ℝ)-Real.sqrt (32/17 : ℝ)/16 := by linarith
  unfold hohmannCost
  rw [example_hohmann, show Real.sqrt (16 : ℝ) = 4 by norm_num]
  rw [abs_of_nonneg h₁, abs_of_nonneg h₂]
  ring

/-- Exact strict margin: over 0.009 times the departure circular speed. -/
theorem finite_bielliptic_saves_deltaV :
    (9/1000 : ℝ) < hohmannCost 16 - cost «example» := by
  rw [example_hohmann_closed, example_cost_closed]
  have hH := example_root_H_bounds
  have hA := example_root_A_bounds
  have hD := example_root_D_bounds
  linarith

theorem finite_bielliptic_beats_hohmann : cost «example» < hohmannCost 16 := by
  linarith [finite_bielliptic_saves_deltaV]

/-- This refutes an unrestricted optimality claim already in a small subclass
of three-burn transfers. It does not identify the all-impulse global optimum. -/
theorem not_universally_best_against_bielliptic :
    ¬ (∀ p : Parameters, hohmannCost p.R ≤ cost p) := by
  intro h
  have hbad := h «example»
  have hgood := finite_bielliptic_beats_hohmann
  change hohmannCost 16 ≤ cost «example» at hbad
  linarith

theorem scaled_counterexample {v : ℝ} (hv : 0 < v) :
    v*cost «example» < v*hohmannCost 16 :=
  mul_lt_mul_of_pos_left finite_bielliptic_beats_hohmann hv

end Bielliptic
end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/Fuel.lean
/- H2 uncompiled candidate. Delta-v is not generally identical to propellant.
This corollary uses one ideal stage, fixed exhaust speed, same initial mass,
no staging/dry-mass changes/refuelling and no other propellant expenditure.
-/

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

-- SOURCE MODULE: HohmannOptimality/PublicStatement.lean
/- H2 uncompiled candidate. Freeze theorem headers before local repair. -/

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

-- SOURCE MODULE: HohmannOptimality/H1Bridge.lean
/- H2 uncompiled candidate. H1 sources are copied byte-for-byte, not re-certified.
This optional layer ties the independent lower bound to H1's physical witness.
-/

noncomputable section
namespace HohmannOptimality

/-- Data conversion only; no optimality assumption is added to H1. -/
def unitsOfH1 (p : HohmannTransfer.Parameters) : Units :=
  ⟨p.mu,p.r₁,p.r₂,p.mu_pos,p.r₁_pos,p.outward⟩

lemma h1_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).speed=HohmannTransfer.circularSpeed p.mu p.r₁ := rfl
lemma h1_outer_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).circular₂=HohmannTransfer.circularSpeed p.mu p.r₂ :=
  (unitsOfH1 p).circular₂_eq_sqrt

lemma h1_peri_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).speed*(unitsOfH1 p).shape.hH=HohmannTransfer.periSpeed p := by
  let u := unitsOfH1 p
  have hs : (u.speed*u.shape.hH)^2=(HohmannTransfer.periSpeed p)^2 := by
    rw [mul_pow, u.speed_sq, u.shape.h_sq, HohmannTransfer.periSpeed_sq]
    dsimp [u, unitsOfH1, Units.shape]
    field_simp [p.r₁_ne, p.r₂_ne, ne_of_gt p.sum_pos]
    ring_nf
    field_simp [ne_of_gt p.sum_pos]
  have hp := mul_pos u.speed_pos u.shape.h_pos
  have hq := HohmannTransfer.periSpeed_pos p
  change u.speed*u.shape.hH=HohmannTransfer.periSpeed p
  nlinarith

lemma h1_apo_speed (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).speed*((unitsOfH1 p).shape.alpha*(unitsOfH1 p).shape.hH)=
      HohmannTransfer.apoSpeed p := by
  let u := unitsOfH1 p
  have hs : (u.speed*(u.shape.alpha*u.shape.hH))^2=(HohmannTransfer.apoSpeed p)^2 := by
    rw [mul_pow, mul_pow, u.speed_sq, u.shape.h_sq, HohmannTransfer.apoSpeed_sq]
    dsimp [u, unitsOfH1, Units.shape]
    field_simp [p.r₁_ne, p.r₂_ne, ne_of_gt p.sum_pos]
    ring_nf
    field_simp [ne_of_gt p.sum_pos]
  have hp := mul_pos u.speed_pos (mul_pos u.shape.alpha_pos u.shape.h_pos)
  have hq := HohmannTransfer.apoSpeed_pos p
  change u.speed*(u.shape.alpha*u.shape.hH)=HohmannTransfer.apoSpeed p
  nlinarith

lemma h1_bound_eq_totalDeltaV (p : HohmannTransfer.Parameters) :
    (unitsOfH1 p).bound=HohmannTransfer.totalDeltaV p := by
  calc
    (unitsOfH1 p).bound =
      ((unitsOfH1 p).speed*(unitsOfH1 p).shape.hH-(unitsOfH1 p).speed) +
      ((unitsOfH1 p).circular₂-(unitsOfH1 p).speed*
        ((unitsOfH1 p).shape.alpha*(unitsOfH1 p).shape.hH)) := by
      dsimp [Units.bound, Units.circular₂, Shape.costH, Shape.burnH₁, Shape.burnH₂]
      ring
    _ = HohmannTransfer.totalDeltaV p := by
      rw [h1_peri_speed, h1_apo_speed, h1_outer_speed, h1_speed]
      rfl

/-- Physical attainment from H1 plus a global lower bound against arbitrary
smooth two-impulse competitors. Free time, free phase, fixed central field. -/
theorem h1_global_two_impulse_minimum (p : HohmannTransfer.Parameters) :
    (∀ t, deriv (deriv (HohmannTransfer.position p)) t =
      -(p.mu/‖HohmannTransfer.position p t‖^3) • HohmannTransfer.position p t) ∧
    HohmannTransfer.position p 0=HohmannTransfer.pack p.r₁ 0 ∧
    HohmannTransfer.position p p.transferTime=HohmannTransfer.pack (-p.r₂) 0 ∧
    (unitsOfH1 p).bound=
      ‖HohmannTransfer.entryImpulse p‖+‖HohmannTransfer.exitImpulse p‖ ∧
    (∀ a : KeplerArc p.mu,
      (a.state a.t₀).radius=p.r₁ → (a.state a.t₁).radius=p.r₂ →
      HohmannTransfer.totalDeltaV p ≤
        (a.state a.t₀).impulse (HohmannTransfer.circularSpeed p.mu p.r₁)+
        (a.state a.t₁).impulse (HohmannTransfer.circularSpeed p.mu p.r₂)) := by
  refine ⟨HohmannTransfer.second_deriv_position p,
    HohmannTransfer.position_departure p,HohmannTransfer.position_arrival p,?_,?_⟩
  · rw [h1_bound_eq_totalDeltaV, HohmannTransfer.totalDeltaV_eq_sum_norms]
  · intro a h₀ h₁
    have h := KeplerArc.newton_arc_lower_bound (unitsOfH1 p) a h₀ h₁
    simpa only [h1_bound_eq_totalDeltaV, h1_speed, h1_outer_speed] using h


/-- The explicit H1 coast is a member of the same class used for the lower bound. -/
def h1KeplerArc (p : HohmannTransfer.Parameters) : KeplerArc p.mu where
  t₀ := 0
  t₁ := p.transferTime
  time_order := p.transferTime_pos
  x := fun t => (HohmannTransfer.position p t).re
  y := fun t => (HohmannTransfer.position p t).im
  vx := fun t => (HohmannTransfer.velocity p t).re
  vy := fun t => (HohmannTransfer.velocity p t).im
  radius_pos := by
    intro t _
    simpa only [Complex.norm_def, Complex.normSq_apply, pow_two] using
      HohmannTransfer.norm_position_pos p t
  dx := by
    intro t _
    exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (HohmannTransfer.hasDerivAt_position p t)
  dy := by
    intro t _
    exact Complex.imCLM.hasFDerivAt.comp_hasDerivAt t (HohmannTransfer.hasDerivAt_position p t)
  dvx := by
    intro t _
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
      (HohmannTransfer.hasDerivAt_velocity_newton p t)
    simpa only [Function.comp_def, Complex.reCLM_apply, HohmannTransfer.gravity,
      Complex.smul_re, smul_eq_mul, Complex.norm_def, Complex.normSq_apply, pow_two, ← neg_div, div_mul_eq_mul_div] using h
  dvy := by
    intro t _
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt t
      (HohmannTransfer.hasDerivAt_velocity_newton p t)
    simpa only [Function.comp_def, Complex.imCLM_apply, HohmannTransfer.gravity,
      Complex.smul_im, smul_eq_mul, Complex.norm_def, Complex.normSq_apply, pow_two, ← neg_div, div_mul_eq_mul_div] using h

lemma h1_state_radius (p : HohmannTransfer.Parameters) (t : ℝ) :
    ((h1KeplerArc p).state t).radius = ‖HohmannTransfer.position p t‖ := by
  simp only [h1KeplerArc, KeplerArc.state, PlanarState.radius, Complex.norm_def,
    Complex.normSq_apply, pow_two]

/-- The lower bound is attained within the actual Newtonian comparison class. -/
theorem h1_attains_bound_in_kepler_class (p : HohmannTransfer.Parameters) :
    ∃ a : KeplerArc p.mu,
      (a.state a.t₀).radius = p.r₁ ∧ (a.state a.t₁).radius = p.r₂ ∧
      (a.state a.t₀).impulse (unitsOfH1 p).speed +
        (a.state a.t₁).impulse (unitsOfH1 p).circular₂ = (unitsOfH1 p).bound := by
  let a := h1KeplerArc p
  have h₀ : (a.state a.t₀).radius = p.r₁ := by
    change ((h1KeplerArc p).state 0).radius = p.r₁
    rw [h1_state_radius, HohmannTransfer.position_departure]
    exact HohmannTransfer.norm_pack_eq p.r₁_pos.le (by ring)
  have h₁ : (a.state a.t₁).radius = p.r₂ := by
    change ((h1KeplerArc p).state p.transferTime).radius = p.r₂
    rw [h1_state_radius, HohmannTransfer.position_arrival]
    exact HohmannTransfer.norm_pack_eq p.r₂_pos.le (by ring)
  have hx₀ : (a.state a.t₀).x = p.r₁ := by
    change (HohmannTransfer.position p 0).re = _
    simp
  have hy₀ : (a.state a.t₀).y = 0 := by
    change (HohmannTransfer.position p 0).im = _
    simp
  have hvx₀ : (a.state a.t₀).vx = 0 := by
    change (HohmannTransfer.velocity p 0).re = _
    simp
  have hvy₀ : (a.state a.t₀).vy = HohmannTransfer.periSpeed p := by
    change (HohmannTransfer.velocity p 0).im = _
    simp
  have hx₁ : (a.state a.t₁).x = -p.r₂ := by
    change (HohmannTransfer.position p p.transferTime).re = _
    simp
  have hy₁ : (a.state a.t₁).y = 0 := by
    change (HohmannTransfer.position p p.transferTime).im = _
    simp
  have hvx₁ : (a.state a.t₁).vx = 0 := by
    change (HohmannTransfer.velocity p p.transferTime).re = _
    simp
  have hvy₁ : (a.state a.t₁).vy = -HohmannTransfer.apoSpeed p := by
    change (HohmannTransfer.velocity p p.transferTime).im = _
    simp
  refine ⟨a, h₀, h₁, ?_⟩
  rw [h1_bound_eq_totalDeltaV, HohmannTransfer.totalDeltaV,
    h1_speed, h1_outer_speed]
  simp only [PlanarState.impulse, h₀, h₁, hx₀, hy₀, hvx₀, hvy₀, hx₁, hy₁, hvx₁, hvy₁,
    mul_zero, zero_div, add_zero, zero_pow (by decide : 2 ≠ 0), zero_add,
    mul_neg, neg_div, mul_div_cancel_right₀ _ p.r₁_ne, mul_div_cancel_right₀ _ p.r₂_ne,
    Real.sqrt_sq_eq_abs]
  change |HohmannTransfer.deltaV₁ p| + _ =
    HohmannTransfer.deltaV₁ p + HohmannTransfer.deltaV₂ p
  rw [abs_of_pos (HohmannTransfer.deltaV₁_pos p)]
  congr 1
  rw [show -HohmannTransfer.apoSpeed p - -HohmannTransfer.circularSpeed p.mu p.r₂ =
    HohmannTransfer.deltaV₂ p by unfold HohmannTransfer.deltaV₂; ring,
    abs_of_pos (HohmannTransfer.deltaV₂_pos p)]

end HohmannOptimality

-- SOURCE MODULE: HohmannOptimality/BiellipticWitness.lean
/- H2 uncompiled candidate. Two finite actual Kepler arcs + three velocity jumps.
The second ellipse is followed from apoapsis to periapsis by a time shift.
-/

noncomputable section
namespace HohmannOptimality
namespace BiellipticWitness
open HohmannTransfer

def first : Parameters := ⟨1,1,64,by norm_num,by norm_num,by norm_num⟩
def second : Parameters := ⟨1,16,64,by norm_num,by norm_num,by norm_num⟩
def direct : Parameters := ⟨1,1,16,by norm_num,by norm_num,by norm_num⟩
def secondPosition (t : ℝ) : ℂ := position second (t+second.transferTime)
def secondVelocity (t : ℝ) : ℂ := velocity second (t+second.transferTime)
def totalTime : ℝ := first.transferTime+second.transferTime

def jump₁ : ℂ := velocity first 0-pack 0 1
def jump₂ : ℂ := secondVelocity 0-velocity first first.transferTime
def jump₃ : ℂ := pack 0 (1/4)-secondVelocity second.transferTime
def cost : ℝ := ‖jump₁‖+‖jump₂‖+‖jump₃‖

lemma secondPosition_deriv (t : ℝ) : HasDerivAt secondPosition (secondVelocity t) t := by
  have hshift : HasDerivAt (fun s : ℝ => s+second.transferTime) 1 t :=
    (hasDerivAt_id t).add_const second.transferTime
  have h := (hasDerivAt_position second (t+second.transferTime)).scomp t hshift
  simpa [secondPosition, secondVelocity, Function.comp_def] using h
lemma secondVelocity_deriv (t : ℝ) :
    HasDerivAt secondVelocity (-(1/‖secondPosition t‖^3) • secondPosition t) t := by
  have hshift : HasDerivAt (fun s : ℝ => s+second.transferTime) 1 t :=
    (hasDerivAt_id t).add_const second.transferTime
  have h := (hasDerivAt_velocity_newton second (t+second.transferTime)).scomp t hshift
  simpa [secondPosition, secondVelocity, gravity, Function.comp_def, show second.mu = 1 from rfl] using h
lemma second_newton (t : ℝ) :
    deriv (deriv secondPosition) t = -(1/‖secondPosition t‖^3) • secondPosition t := by
  have hd : deriv secondPosition=secondVelocity := funext (fun s => (secondPosition_deriv s).deriv)
  rw [hd]
  exact (secondVelocity_deriv t).deriv
lemma second_start : secondPosition 0=pack (-64) 0 := by
  simp [secondPosition, second]
lemma second_end : secondPosition second.transferTime=pack 16 0 := by
  have h := position_periodic second 0
  simpa [secondPosition, two_mul, second] using h
lemma second_velocity_start : secondVelocity 0=pack 0 (-apoSpeed second) := by
  simp [secondVelocity]
lemma second_velocity_end : secondVelocity second.transferTime=pack 0 (periSpeed second) := by
  have h := velocity_periodic second 0
  simpa [secondVelocity, two_mul] using h
lemma junction : position first first.transferTime=secondPosition 0 := by
  rw [second_start, position_arrival]
  rfl
lemma time_pos : 0 < totalTime := add_pos first.transferTime_pos second.transferTime_pos

lemma first_peri : periSpeed first=Real.sqrt (128/65 : ℝ) := by
  rw [periSpeed_formula]
  norm_num [first]
lemma second_peri : periSpeed second=Real.sqrt (1/10 : ℝ) := by
  rw [periSpeed_formula]
  norm_num [second]
lemma first_apo : apoSpeed first=Real.sqrt (128/65 : ℝ)/64 := by
  have hs : apoSpeed first ^ 2 = (1/2080 : ℝ) := by
    rw [apoSpeed_sq]
    norm_num [first]
  have hroot : (Real.sqrt (128/65 : ℝ)/64) ^ 2 = (1/2080 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 128/65)]
    norm_num
  have hnonneg : 0 ≤ Real.sqrt (128/65 : ℝ)/64 := by positivity
  nlinarith [apoSpeed_pos first, hnonneg, hs.trans hroot.symm]
lemma second_apo : apoSpeed second=Real.sqrt (1/10 : ℝ)/4 := by
  have hs : apoSpeed second ^ 2 = (1/160 : ℝ) := by
    rw [apoSpeed_sq]
    norm_num [second]
  have hroot : (Real.sqrt (1/10 : ℝ)/4) ^ 2 = (1/160 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1/10)]
    norm_num
  have hnonneg : 0 ≤ Real.sqrt (1/10 : ℝ)/4 := by positivity
  nlinarith [apoSpeed_pos second, hnonneg, hs.trans hroot.symm]
lemma direct_peri : periSpeed direct=Real.sqrt (32/17 : ℝ) := by
  rw [periSpeed_formula]
  norm_num [direct]
lemma direct_apo : apoSpeed direct=Real.sqrt (32/17 : ℝ)/16 := by
  have hs : apoSpeed direct ^ 2 = (1/136 : ℝ) := by
    rw [apoSpeed_sq]
    norm_num [direct]
  have hroot : (Real.sqrt (32/17 : ℝ)/16) ^ 2 = (1/136 : ℝ) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 32/17)]
    norm_num
  have hnonneg : 0 ≤ Real.sqrt (32/17 : ℝ)/16 := by positivity
  nlinarith [apoSpeed_pos direct, hnonneg, hs.trans hroot.symm]
lemma direct_cost : totalDeltaV direct=Bielliptic.hohmannCost 16 := by
  rw [Bielliptic.example_hohmann_closed]
  unfold totalDeltaV deltaV₁ deltaV₂
  rw [direct_peri, direct_apo]
  norm_num [circularSpeed, direct]
  ring

lemma jump₁_norm : ‖jump₁‖=|Real.sqrt (128/65 : ℝ)-1| := by
  unfold jump₁
  rw [velocity_departure, first_peri, pack_sub, sub_self, norm_pack_vertical]
lemma jump₂_norm : ‖jump₂‖=|Real.sqrt (1/10 : ℝ)/4-Real.sqrt (128/65 : ℝ)/64| := by
  unfold jump₂
  rw [second_velocity_start, velocity_arrival, first_apo, second_apo, pack_sub]
  norm_num only [sub_self]
  rw [norm_pack_vertical]
  have h : -(Real.sqrt (1/10 : ℝ)/4)-(-(Real.sqrt (128/65 : ℝ)/64))=
      -(Real.sqrt (1/10 : ℝ)/4-Real.sqrt (128/65 : ℝ)/64) := by ring
  rw [h, abs_neg]
lemma jump₃_norm : ‖jump₃‖=|Real.sqrt (1/10 : ℝ)-(1/4 : ℝ)| := by
  unfold jump₃
  rw [second_velocity_end, second_peri, pack_sub]
  norm_num only [sub_self]
  rw [norm_pack_vertical, abs_sub_comm]
lemma cost_eq : cost=Bielliptic.cost Bielliptic.«example» := by
  rw [cost, jump₁_norm, jump₂_norm, jump₃_norm]
  unfold Bielliptic.cost Bielliptic.firstApoSpeed Bielliptic.secondApoSpeed
  rw [Bielliptic.example_departure, Bielliptic.example_arrival]
  norm_num [Bielliptic.«example»]
  congr 2 <;> ring

/-- The numerical comparison is linked to actual finite-time coast arcs and
actual vector jump norms. No arrival time or third burn is sent to infinity. -/
theorem physical_three_impulse_counterexample :
    0 < totalTime ∧
    (∀ t, deriv (deriv (position first)) t =
      -(1/‖position first t‖^3) • position first t) ∧
    (∀ t, deriv (deriv secondPosition) t =
      -(1/‖secondPosition t‖^3) • secondPosition t) ∧
    position first 0=pack 1 0 ∧
    position first first.transferTime=secondPosition 0 ∧
    secondPosition second.transferTime=pack 16 0 ∧
    (9/1000 : ℝ) < totalDeltaV direct-(‖jump₁‖+‖jump₂‖+‖jump₃‖) := by
  refine ⟨time_pos,?_,second_newton,?_,junction,second_end,?_⟩
  · intro t
    exact second_deriv_position first t
  · exact position_departure first
  · change (9/1000 : ℝ) < totalDeltaV direct-cost
    rw [direct_cost, cost_eq]
    exact Bielliptic.finite_bielliptic_saves_deltaV

end BiellipticWitness
end HohmannOptimality
