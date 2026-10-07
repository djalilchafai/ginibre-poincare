module

public import GinibrePoincare.Analysis.MatrixOverlapGradientIntegrability
public import GinibrePoincare.Analysis.GinibreC1WeakPoincare

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The matrix-lift Poincaré inequality for every symmetric C¹ observable
with genuine finite L² value and finite overlap energy. The spectral law,
weak-domain membership, and overlap domination are derived internally. -/
theorem matrixSpectralLift_finite_overlap_poincare {n : ℕ} (hn : 0 < n)
    (F : Configuration n → ℝ) (hF : ContDiff ℝ 1 F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n))
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    smoothGinibreVariance n F ≤
      (2 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  have hd := hF.differentiable (by norm_num)
  have hgl := matrixOverlap_finite_gradient_memLp hn F hd hsym hE
  have hpi := ginibre_C1_finite_energy_poincare hn F hF hsym hFL2 hgl
  have hgrad := (matrixOverlap_finite_gradient_energy hn F hd hsym hE).2
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  calc
    smoothGinibreVariance n F ≤
        (1 / (2 * (n : ℝ))) * ∫ z, realGradientNormSq F z ∂ginibreMeasure n := hpi
    _ ≤ (1 / (2 * (n : ℝ))) *
        (4 * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n) :=
      mul_le_mul_of_nonneg_left hgrad (by positivity)
    _ = _ := by field_simp; ring

#print axioms matrixSpectralLift_finite_overlap_poincare
end
end GinibrePoincare
