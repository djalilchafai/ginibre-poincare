module

public import GinibrePoincare.Analysis.PolarGaussianMoments
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- Radial Jacobian of the normalized regularized logarithmic Laplacian. -/
def correspondenceLogRadial (τ r : ℝ) : ℝ := τ*r/(Real.pi*(r^2+τ)^2)

private def radialPrimitive (τ r : ℝ) : ℝ := -τ/(2*Real.pi*(r^2+τ))

private theorem radialPrimitive_deriv {τ : ℝ} (hτ : 0 < τ) (r : ℝ) :
    HasDerivAt (radialPrimitive τ) (correspondenceLogRadial τ r) r := by
  have hd : HasDerivAt (fun x : ℝ => 2*Real.pi*(x^2+τ))
      (2*Real.pi*(2*r)) r := by
    convert (((hasDerivAt_id r).pow 2).add_const τ).const_mul (2*Real.pi) using 1 <;> simp
  have hden : 2*Real.pi*(r^2+τ) ≠ 0 := by positivity
  have h := (hasDerivAt_const r (-τ)).div hd hden
  convert h using 1
  · funext x; rfl
  · unfold correspondenceLogRadial
    field_simp
    ring

private theorem radialPrimitive_limit (τ : ℝ) :
    Tendsto (radialPrimitive τ) atTop (𝓝 0) := by
  have h : Tendsto (fun r : ℝ => r^2+τ) atTop atTop :=
    tendsto_atTop_add_const_right atTop τ (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0))
  have hi := h.inv_tendsto_atTop
  have heq : radialPrimitive τ = fun r : ℝ => (-τ*(2*Real.pi)⁻¹)*(r^2+τ)⁻¹ := by
    funext r
    unfold radialPrimitive
    rw [div_eq_mul_inv, mul_inv]
    ring
  rw [heq]
  simpa using hi.const_mul (-τ*(2*Real.pi)⁻¹)

theorem correspondenceLogRadial_integrable {τ a : ℝ} (hτ : 0 < τ) (ha : 0 ≤ a) :
    IntegrableOn (correspondenceLogRadial τ) (Ioi a) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun r hr => radialPrimitive_deriv hτ r)
    (fun r hr => by
      have hr0 : 0 ≤ r := ha.trans hr.le
      dsimp [correspondenceLogRadial]; positivity)
    (radialPrimitive_limit τ)

theorem correspondenceLogRadial_integral {τ a : ℝ} (hτ : 0 < τ) (ha : 0 ≤ a) :
    (∫ r in Ioi a, correspondenceLogRadial τ r) = τ/(2*Real.pi*(a^2+τ)) := by
  have h := integral_Ioi_of_hasDerivAt_of_nonneg'
    (fun r (hr : r ∈ Ici a) => radialPrimitive_deriv hτ r)
    (fun r (hr : r ∈ Ioi a) => by
      have hr0 : 0 ≤ r := ha.trans hr.le
      dsimp [correspondenceLogRadial]; positivity)
    (radialPrimitive_limit τ)
  simpa [radialPrimitive, neg_div] using h

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceLogRadial_integrable
#print axioms GinibrePoincare.correspondenceLogRadial_integral
