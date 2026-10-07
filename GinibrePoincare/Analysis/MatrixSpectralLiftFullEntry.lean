module

public import GinibrePoincare.Analysis.MatrixSpectralLiftEntryAE
public import GinibrePoincare.Analysis.MatrixSpectralSobolevLift
public import GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

def matrixEntryFullSpectralLift {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (F : (Fin n → ℂ) → ℝ) : Configuration m → ℝ :=
  fun x => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e x))

theorem matrixEntryFullSpectralLift_derivative_eq_simple {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (x : Configuration m) (hx : (Matrix.of (matrixComplexEntryEquiv e x)).charpoly.Separable)
    (i : Fin m × Fin 2) :
    fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i) =
      matrixEntryIntrinsicSpectralGradient e F x i := by
  have hf := matrixFullSymmetricSpectralLift_differentiableAt n (matrixComplexEntryEquiv e x) hx F hF hsym
  have hc := hf.hasFDerivAt.comp x (matrixComplexEntryEquiv e).hasFDerivAt
  change (fderiv ℝ ((fun A : MatrixRealSpace n => matrixFullSymmetricSpectralLift n F (Matrix.of A)) ∘
    matrixComplexEntryEquiv e) x) (ginibreCoordinateDirection i) = _
  rw [hc.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [matrixComplexEntryEquiv_direction]
  have he := (matrixFullSymmetricSpectralLift_eventually_eq_simple n (matrixComplexEntryEquiv e x) hx F hsym).fderiv_eq
    (𝕜 := ℝ)
  rw [he]
  rfl

theorem matrixEntryFullSpectralLift_derivative_ae {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z) (i : Fin m × Fin 2) :
    (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i))
      =ᵐ[matrixEntryGaussianMeasure e] (fun x => matrixEntryIntrinsicSpectralGradient e F x i) := by
  filter_upwards [(matrixComplexEntryEquiv_gaussian_preserving hn e).quasiMeasurePreserving.ae
    (matrixGaussian_charpoly_separable_ae n)] with x hx
  exact matrixEntryFullSpectralLift_derivative_eq_simple e F hF hsym x hx i

theorem matrixEntryFullSpectralLift_derivative_memLp {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) (i : Fin m × Fin 2) :
    MemLp (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i)) 2
      (matrixEntryGaussianMeasure e) := by
  have hvec := matrixEntryIntrinsicSpectralGradient_memLp hn e F hF hsym hE
  have hscalar := (memLp_piLp_iff.mp hvec) i
  exact hscalar.ae_eq (matrixEntryFullSpectralLift_derivative_ae hn e F hF hsym i).symm

theorem matrixEntryFullSpectralLift_derivative_locallyIntegrable {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (hE : Integrable (matrixSpectralOverlapEnergy n F) (matrixGaussianMeasure n)) (i : Fin m × Fin 2) :
    LocallyIntegrable (fun x => fderiv ℝ (matrixEntryFullSpectralLift e F) x (ginibreCoordinateDirection i)) volume := by
  letI := matrixEntryGaussianMeasure_isProbability hn e
  have hi := (matrixEntryFullSpectralLift_derivative_memLp hn e F hF hsym hE i).integrable (by norm_num)
  rw [matrixEntryGaussianMeasure_eq_real_density e] at hi
  exact positive_density_integrable_locallyIntegrable volume (matrixEntryGaussianDensityReal e) _
    (matrixEntryGaussianDensityReal_continuous e) (matrixEntryGaussianDensityReal_pos hn e) hi

#print axioms matrixEntryFullSpectralLift_derivative_locallyIntegrable
end
end GinibrePoincare
