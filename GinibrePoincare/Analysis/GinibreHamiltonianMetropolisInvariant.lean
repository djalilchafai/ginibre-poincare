module

public import GinibrePoincare.Analysis.GinibreHamiltonianMetropolisBalance

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem metropolisReversibleKernel_lintegral_invariant {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (q : E → E → ℝ≥0∞)
    (hq : Measurable (Function.uncurry q)) (hNorm : ∀ x, ∫⁻ y, q x y ∂μ=1)
    (φ : E → ℝ≥0∞) (hφ : Measurable φ) :
    (∫⁻ x, ∫⁻ y, φ y ∂metropolisReversibleKernel μ q x ∂μ)=∫⁻ x, φ x ∂μ := by
  have hs := metropolisAcceptedFlux_measurable q hq
  have hsm (x : E) : Measurable (metropolisAcceptedFlux q x) := hs.comp measurable_prodMk_left
  have hr := metropolisRejectionMass_measurable μ q hq
  have hflux : (∫⁻ x, ∫⁻ y, metropolisAcceptedFlux q x y*φ y ∂μ ∂μ)=
      ∫⁻ x, φ x*(∫⁻ y, metropolisAcceptedFlux q x y ∂μ) ∂μ := by
    rw [← lintegral_prod (fun p : E × E => metropolisAcceptedFlux q p.1 p.2*φ p.2)
      (hs.mul (hφ.comp measurable_snd)).aemeasurable,
      metropolisAcceptedFlux_balance μ q (fun p => φ p.2)]
    simp only [Prod.snd_swap]
    rw [lintegral_prod (fun p : E × E => metropolisAcceptedFlux q p.1 p.2*φ p.1)
      (hs.mul (hφ.comp measurable_fst)).aemeasurable]
    apply lintegral_congr
    intro x
    simp only [Prod.snd_swap]
    simp_rw [mul_comm (metropolisAcceptedFlux q x _) (φ x)]
    exact lintegral_const_mul (φ x) (hsm x)
  simp_rw [metropolisReversibleKernel_apply μ q hq, lintegral_add_measure,
    lintegral_withDensity_eq_lintegral_mul μ (hsm _) hφ, lintegral_smul_measure,
    lintegral_dirac' _ hφ, smul_eq_mul]
  simp only [Pi.mul_apply]
  rw [lintegral_add_left (hs.mul (hφ.comp measurable_snd)).lintegral_prod_right, hflux]
  have hp : Measurable (fun x => φ x*(∫⁻ y, metropolisAcceptedFlux q x y ∂μ)) :=
    hφ.mul hs.lintegral_prod_right
  rw [← lintegral_add_left hp]
  apply lintegral_congr
  intro x
  rw [metropolisRejectionMass, mul_comm _ (φ x),← mul_add]
  congr 1
  rw [add_tsub_cancel_of_le]
  · simp
  · calc
      (∫⁻ y, metropolisAcceptedFlux q x y ∂μ) ≤ ∫⁻ y, q x y ∂μ := lintegral_mono (fun y => min_le_left _ _)
      _=1 := hNorm x

end
end GinibrePoincare
