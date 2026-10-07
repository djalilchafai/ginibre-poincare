module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevContinuity
public import GinibrePoincare.Analysis.MatrixSymmetricLift

@[expose] public section

/-! # Continuous collision extension of the actual measurable spectral lift -/
open Matrix MeasureTheory Filter
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixAllEigenvalues_injective_of_separable (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℂ) (hs : A.charpoly.Separable) :
    Function.Injective (matrixAllEigenvalues n A) := by
  have h := Polynomial.nodup_roots hs
  rw [← matrix_full_roots_configuration_multiset A (matrixAllEigenvalues n A)
    (matrixAllEigenvalues_charpoly n A)] at h
  have hi := (Multiset.nodup_map_iff_inj_on Finset.univ.nodup).mp h
  intro i j hij
  exact hi i (by simp) j (by simp) hij

theorem matrixFullSymmetricSpectralLift_eq_simple (n : ℕ)
    (A : GinibreMatrixCoordinates n) (hs : (Matrix.of A).charpoly.Separable)
    (F : (Fin n → ℂ) → ℝ)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    matrixFullSymmetricSpectralLift n F (Matrix.of A) = matrixSymmetricLift n F A := by
  have hc := matrixMeasurableEigenvalues_spec n A hs
  exact matrixSimpleSpectrum_symmetric_value n (Matrix.of A) hs
    (matrixAllEigenvalues n (Matrix.of A)) (matrixMeasurableEigenvalues n A)
    (matrixAllEigenvalues_injective_of_separable n (Matrix.of A) hs) hc.1
    (fun i => (matrixAllEigenvalues_isRoot n (Matrix.of A) i).eq_zero) hc.2 F hsym

theorem matrixFullSymmetricSpectralLift_eq_ae (n : ℕ)
    (F : (Fin n → ℂ) → ℝ)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    (fun A : GinibreMatrixCoordinates n => matrixFullSymmetricSpectralLift n F (Matrix.of A))
      =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F := by
  filter_upwards [matrixGaussian_charpoly_separable_ae n] with A hA
  exact matrixFullSymmetricSpectralLift_eq_simple n A hA F hsym

/-- Near a simple spectrum, the continuous collision extension agrees with the
original measurable-label lift throughout an actual open neighborhood. -/
theorem matrixFullSymmetricSpectralLift_eventually_eq_simple (n : ℕ)
    (A : GinibreMatrixCoordinates n) (hs : (Matrix.of A).charpoly.Separable)
    (F : (Fin n → ℂ) → ℝ)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    (fun B : GinibreMatrixCoordinates n => matrixFullSymmetricSpectralLift n F (Matrix.of B))
      =ᶠ[𝓝 A] matrixSymmetricLift n F := by
  obtain ⟨U, labels, ho, hA, hd, hr⟩ :=
    matrixSimpleSpectrum_exists_smooth_local_labeling n A hs
  filter_upwards [ho.mem_nhds hA] with B hB
  exact matrixFullSymmetricSpectralLift_eq_simple n B
    (matrix_injective_full_roots_separable n (Matrix.of B) (labels B)
      (hr B hB).1 (hr B hB).2) F hsym

theorem matrixFullSymmetricSpectralLift_differentiableAt (n : ℕ)
    (A : GinibreMatrixCoordinates n) (hs : (Matrix.of A).charpoly.Separable)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    DifferentiableAt ℝ
      (fun B : GinibreMatrixCoordinates n => matrixFullSymmetricSpectralLift n F (Matrix.of B)) A := by
  exact (matrixSymmetricLift_differentiableAt n A hs F hF hsym).congr_of_eventuallyEq
    (matrixFullSymmetricSpectralLift_eventually_eq_simple n A hs F hsym)

theorem matrixFullSymmetricSpectralLift_energy (n : ℕ)
    (A : GinibreMatrixCoordinates n) (hs : (Matrix.of A).charpoly.Separable)
    (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    matrixRealGradientEnergy n
      (fun B : GinibreMatrixCoordinates n => matrixFullSymmetricSpectralLift n F (Matrix.of B)) A =
      4 * matrixSpectralOverlapEnergy n F A := by
  have heq := (matrixFullSymmetricSpectralLift_eventually_eq_simple n A hs F hsym).fderiv_eq
    (𝕜 := ℝ)
  unfold matrixRealGradientEnergy directionalEnergy
  rw [heq]
  exact matrixSymmetricLift_energy n A hs F hF hsym

end
end GinibrePoincare
