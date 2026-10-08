module
public import GinibrePoincare.Analysis.GinibrePointwiseBochner
public import GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential
@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff BigOperators ComplexConjugate Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem correspondenceBochnerGradient_coordinate {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) (j : Fin n) :
    ginibreBochnerGradient f z j =
      (bochnerDirectionalDerivative (realCoordinateDirection j) f z : ℂ) +
        Complex.I * (bochnerDirectionalDerivative (imaginaryCoordinateDirection j) f z : ℂ) := by
  simp [Finset.sum_add_distrib,eq_comm,mul_comm,ginibreBochnerGradient,Fintype.sum_prod_type,Fin.sum_univ_two,
    ginibreBochnerDirection,realCoordinateDirection,imaginaryCoordinateDirection,
    coordinateDirection,Complex.real_smul,sum_apply]

theorem correspondenceBochnerGradient_normSq {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) :
    configurationNormSq (ginibreBochnerGradient f z) =
      ∑ i : Fin n × Fin 2, (bochnerDirectionalDerivative (ginibreBochnerDirection i) f z)^2 := by
  simp only [configurationNormSq,correspondenceBochnerGradient_coordinate,
    Fintype.sum_prod_type,Fin.sum_univ_two,ginibreBochnerDirection]
  simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,pow_two]

theorem correspondenceGamma_gradient_normSq {n : ℕ} (hn : 0<n)
    (f : Configuration n → ℝ) (hf : ContDiff ℝ ∞ f) (z : Configuration n) (hz : CollisionFree z) :
    (n : ℝ)*ginibrePointwiseGamma n f f z = configurationNormSq (ginibreBochnerGradient f z) := by
  rw [ginibrePointwiseGamma_eq hn f f hf hf z hz,correspondenceBochnerGradient_normSq]
  simp only [← pow_two]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp

#print axioms correspondenceGamma_gradient_normSq
#print axioms correspondenceBochnerGradient_normSq
end
end GinibrePoincare
