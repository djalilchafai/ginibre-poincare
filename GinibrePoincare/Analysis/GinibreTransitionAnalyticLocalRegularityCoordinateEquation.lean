module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCoordinates
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityProduct

@[expose] public section
open MeasureTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

theorem ginibreLocalRegularity_coordinate_directional (n : ℕ)
    (θ : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ) (hθ : ContDiff ℝ ∞ θ)
    (z : Configuration n) (v : EuclideanSpace ℝ (Fin n × Fin 2)) :
    fderiv ℝ (θ ∘ configurationEuclideanEquiv n) z ((configurationEuclideanEquiv n).symm v) =
      fderiv ℝ θ (configurationEuclideanEquiv n z) v := by
  have h := ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp z
    (configurationEuclideanEquiv n).hasFDerivAt
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply] using congrArg (fun L => L ((configurationEuclideanEquiv n).symm v)) h.fderiv

theorem ginibreLocalRegularity_coordinate_elliptic_equation
    (n : ℕ) {ι : Type*} [Fintype ι]
    (v : ι → EuclideanSpace ℝ (Fin n × Fin 2))
    (U : Set (Configuration n)) (u h : Configuration n → ℂ) (F : ι → Configuration n → ℂ)
    (heq : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U →
      (∫ z, u z*ginibreLocalRegularityLaplacian (fun i => (configurationEuclideanEquiv n).symm (v i)) θ z) =
        (∫ z, h z*θ z)-∑ i, ∫ z, F i z*ginibreLocalRegularityDirectional ((configurationEuclideanEquiv n).symm (v i)) θ z) :
    ∀ θ : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ (configurationEuclideanEquiv n) '' U →
      (∫ x, u ((configurationEuclideanEquiv n).symm x)*ginibreLocalRegularityLaplacian v θ x) =
        (∫ x, h ((configurationEuclideanEquiv n).symm x)*θ x)-
        ∑ i, ∫ x, F i ((configurationEuclideanEquiv n).symm x)*ginibreLocalRegularityDirectional (v i) θ x := by
  classical
  intro θ hθ hc hs
  let e := configurationEuclideanEquiv n
  let ψ := θ ∘ e
  have hψ : ContDiff ℝ ∞ ψ := hθ.comp e.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph e.toHomeomorph
  have hψs : tsupport ψ ⊆ U := by
    intro z hz
    have hx : e z ∈ tsupport θ := by
      exact (Set.ext_iff.mp (tsupport_comp_eq_preimage θ e.toHomeomorph) z).mp hz
    obtain ⟨y,hy,he⟩ := hs hx
    exact e.injective he ▸ hy
  have hd (z) (i) : ginibreLocalRegularityDirectional (e.symm (v i)) ψ z =
      ginibreLocalRegularityDirectional (v i) θ (e z) := ginibreLocalRegularity_coordinate_directional n θ hθ z (v i)
  have hdd (z) (i) : ginibreLocalRegularityDirectional (e.symm (v i))
      (ginibreLocalRegularityDirectional (e.symm (v i)) ψ) z =
      ginibreLocalRegularityDirectional (v i) (ginibreLocalRegularityDirectional (v i) θ) (e z) := by
    have he : ginibreLocalRegularityDirectional (e.symm (v i)) ψ =
        ginibreLocalRegularityDirectional (v i) θ ∘ e := by funext y; exact hd y i
    rw [he]
    exact ginibreLocalRegularity_coordinate_directional n _ (ginibreLocalRegularityDirectional_smooth θ hθ (v i)) z (v i)
  have hl (z) : ginibreLocalRegularityLaplacian (fun i => e.symm (v i)) ψ z =
      ginibreLocalRegularityLaplacian v θ (e z) := by
    unfold ginibreLocalRegularityLaplacian
    simp_rw [hdd]
  have he := heq ψ hψ hψc hψs
  change (∫ z, u z*ginibreLocalRegularityLaplacian (fun i => e.symm (v i)) ψ z) =
    (∫ z, h z*ψ z)-∑ i, ∫ z, F i z*ginibreLocalRegularityDirectional (e.symm (v i)) ψ z at he
  simp_rw [hl,hd] at he
  obtain ⟨c,hcpos,hchange⟩ := ginibreLocalRegularity_coordinate_integral n
  have hi (f : Configuration n → ℂ) (q : EuclideanSpace ℝ (Fin n × Fin 2) → ℂ) :
      (∫ z, f z*q (e z)) = (c : ℝ) • (∫ x, f (e.symm x)*q x) := by
    have hh := hchange (fun x => f (e.symm x)*q x)
    simpa only [e,ContinuousLinearEquiv.symm_apply_apply] using hh
  dsimp only [ψ, Function.comp_apply] at he
  rw [hi u _,hi h _] at he
  simp_rw [hi (F _) _,← Finset.smul_sum] at he
  have hcn : (c : ℝ) ≠ 0 := (show 0 < (c : ℝ) from hcpos).ne'
  have hh := congrArg (fun w : ℂ => (c : ℝ)⁻¹ • w) he
  simpa only [smul_sub,smul_smul,inv_mul_cancel₀ hcn,one_smul] using hh

#print axioms ginibreLocalRegularity_coordinate_elliptic_equation
end
end GinibrePoincare
