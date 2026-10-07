module

public import GinibrePoincare.Analysis.MatrixSpectralLiftLSITransport

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- Finite actual overlap integral gives genuine L2 integrability of every real
matrix-entry derivative of the intrinsic spectral lift. -/
theorem matrixSpectralLift_gradient_memLp {n : ℕ}
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n))
    (i : MatrixRealIndex n) :
    MemLp (fun A : MatrixRealSpace n => fderiv ℝ (matrixSymmetricLift n F) A
      (matrixRealCoordinates n (Pi.single i 1))) 2 (matrixGaussianMeasure n) := by
  have hg : Integrable (matrixRealGradientEnergy n (matrixSymmetricLift n F))
      (matrixGaussianMeasure n) := by
    apply (hE.const_mul 4).congr
    filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
    exact (matrixSymmetricLift_energy n A hA F hF hsym).symm
  have hd : Measurable (fun A : MatrixRealSpace n => fderiv ℝ (matrixSymmetricLift n F) A
      (matrixRealCoordinates n (Pi.single i 1))) := by
    have hm := measurable_fderiv ℝ (matrixSymmetricLift n F)
    fun_prop
  apply (memLp_two_iff_integrable_sq hd.aestronglyMeasurable).mpr
  apply hg.mono' (hd.pow_const 2).aestronglyMeasurable
  apply ae_of_all (matrixGaussianMeasure n)
  intro A
  change ‖(fderiv ℝ (matrixSymmetricLift n F) A
    (matrixRealCoordinates n (Pi.single i 1))) ^ 2‖ ≤
      matrixRealGradientEnergy n (matrixSymmetricLift n F) A
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (fderiv ℝ (matrixSymmetricLift n F) A
    (matrixRealCoordinates n (Pi.single i 1))))]
  unfold matrixRealGradientEnergy directionalEnergy
  exact Finset.single_le_sum (fun j hj => sq_nonneg (fderiv ℝ (matrixSymmetricLift n F) A
    (matrixRealCoordinates n (Pi.single j 1)))) (Finset.mem_univ i)

#print axioms matrixSpectralLift_gradient_memLp
end
end GinibrePoincare
