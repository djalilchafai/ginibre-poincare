module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateLp
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinateBasis

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

theorem ginibreLocalRegularity_coordinate_weak_derivative
    (n : ℕ) (w : Configuration n → ℂ)
    (g : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin n × Fin 2))))
    (k : Fin n × Fin 2)
    (hg : ∀ θ : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, θ x*g x) = -(∫ x, fderiv ℝ θ x (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k)*
        w ((configurationEuclideanEquiv n).symm x))) :
    MemLp (fun z => g (configurationEuclideanEquiv n z)) 2 (volume : Measure (Configuration n)) ∧
    ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ z, θ z*g (configurationEuclideanEquiv n z)) =
        -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*w z) := by
  refine ⟨ginibreLocalRegularity_coordinate_pullback_memLp n g (MeasureTheory.Lp.memLp g),?_⟩
  intro θ hθ hc
  let e := configurationEuclideanEquiv n
  let ψ := θ ∘ e.symm
  have hψ : ContDiff ℝ ∞ ψ := hθ.comp e.symm.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.symm.toHomeomorph
  have hd (x) : fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k) =
      fderiv ℝ θ (e.symm x) (ginibreCoordinateDirection k) := by
    have hh := ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp x e.symm.hasFDerivAt
    have he := congrArg (fun L => L (EuclideanSpace.basisFun (Fin n × Fin 2) ℝ k)) hh.fderiv
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      e,ψ,ginibreLocalRegularity_coordinate_basis] using he
  have he := hg ψ hψ hψc
  simp_rw [hd] at he
  obtain ⟨c,hcpos,hchange⟩ := ginibreLocalRegularity_coordinate_integral n
  have hl := hchange (fun x => θ (e.symm x)*g x)
  have hr := hchange (fun x => fderiv ℝ θ (e.symm x) (ginibreCoordinateDirection k)*w (e.symm x))
  simp only [e,ContinuousLinearEquiv.symm_apply_apply] at hl hr
  rw [hl]
  rw [show (∫ x, θ (e.symm x)*g x) = ∫ x, ψ x*g x by rfl,he,smul_neg]
  rw [hr]

#print axioms ginibreLocalRegularity_coordinate_weak_derivative
end
end GinibrePoincare
