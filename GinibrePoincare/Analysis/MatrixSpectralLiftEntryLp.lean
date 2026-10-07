module

public import GinibrePoincare.Analysis.MatrixSpectralLiftGradientLp
public import GinibrePoincare.Analysis.MatrixSpectralSobolevDensityTransport
public import GinibrePoincare.Analysis.MatrixSpectralSobolevDirections

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def matrixEntryIntrinsicSpectralGradient {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (F : (Fin n → ℂ) → ℝ) (x : Configuration m) : EuclideanSpace ℝ (Fin m × Fin 2) :=
  WithLp.toLp 2 (fun i => fderiv ℝ (matrixSymmetricLift n F) (matrixComplexEntryEquiv e x)
    (matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e i) 1)))

theorem matrixEntryIntrinsicSpectralGradient_memLp {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) :
    MemLp (matrixEntryIntrinsicSpectralGradient e F) 2 (matrixEntryGaussianMeasure e) := by
  apply memLp_piLp_iff.mpr
  intro i
  exact (matrixSpectralLift_gradient_memLp F hF hsym hE (matrixEntryRealIndexEquiv e i)).comp_measurePreserving
    (matrixComplexEntryEquiv_gaussian_preserving hn e)

theorem matrixEntryIntrinsicSpectralValue_memLp {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Measurable F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hFL2 : MemLp F 2 (ginibreMeasure n)) :
    MemLp (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)) 2
      (matrixEntryGaussianMeasure e) :=
  ((matrixSpectralLift_memLp_two_iff hn F hF hsym).mpr hFL2).comp_measurePreserving
    (matrixComplexEntryEquiv_gaussian_preserving hn e)

#print axioms matrixEntryIntrinsicSpectralGradient_memLp
end
end GinibrePoincare
