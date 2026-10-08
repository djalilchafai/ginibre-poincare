module
public import GinibrePoincare.Analysis.CorrespondenceCurvatureHessian
@[expose] public section
open Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Literal interaction-only pointwise deficit identity (1.43). -/
theorem correspondence_pointwise_interaction_deficit {n : ℕ} (hn : 0<n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
    ginibrePointwiseGammaTwo n f z - 2*ginibrePointwiseGamma n f f z =
      (1/(n : ℝ)^2)*(ginibreBochnerHessianSquare f z +
        fderiv ℝ (fderiv ℝ (ginibreInteractionPotential n)) z
          (ginibreBochnerGradient f z) (ginibreBochnerGradient f z)) := by
  have hG := correspondenceGamma_gradient_normSq hn f hf z hz
  have hB := ginibrePointwiseGammaTwo_bochner_bilinear hn f hf z hz
  rw [correspondence_hamiltonian_interaction_hessian _ _ _ hz] at hB
  have hs : (∑ j, (conj (ginibreBochnerGradient f z j)*ginibreBochnerGradient f z j).re) =
      configurationNormSq (ginibreBochnerGradient f z) := by
    simp [configurationNormSq,Complex.mul_re,Complex.normSq_apply,pow_two]
  rw [hs,← hG] at hB
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  apply (mul_left_cancel₀ (pow_ne_zero 2 hn0))
  field_simp
  nlinarith [hB]

#print axioms correspondence_pointwise_interaction_deficit
end
end GinibrePoincare
