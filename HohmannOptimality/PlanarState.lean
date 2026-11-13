/- H2 uncompiled candidate. Euclidean, NOT a product-type sup-norm. -/
import HohmannOptimality.PhysicalUnits

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
