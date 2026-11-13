/-
Authors: Qianli Ma
A finite three-burn competitor, not an infinite limit. -/
import HohmannOptimality.Shape

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
