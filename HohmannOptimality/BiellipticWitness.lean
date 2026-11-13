/-
Authors: Qianli Ma
Two finite actual Kepler arcs + three velocity jumps.
The second ellipse is followed from apoapsis to periapsis by a time shift.
-/
import HohmannOptimality.H1Bridge

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
  rw [one_smul] at h
  exact h
lemma secondVelocity_deriv (t : ℝ) :
    HasDerivAt secondVelocity (-(1/‖secondPosition t‖^3) • secondPosition t) t := by
  have hshift : HasDerivAt (fun s : ℝ => s+second.transferTime) 1 t :=
    (hasDerivAt_id t).add_const second.transferTime
  have h := (hasDerivAt_velocity_newton second (t+second.transferTime)).scomp t hshift
  rw [one_smul] at h
  exact h
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
