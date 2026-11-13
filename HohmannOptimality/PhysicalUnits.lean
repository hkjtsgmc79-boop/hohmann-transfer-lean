/- H2 uncompiled candidate. Restore arbitrary positive μ and length scale. -/
import HohmannOptimality.EndpointOptimality

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
