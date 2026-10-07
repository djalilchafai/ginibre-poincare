module

public import GinibrePoincare.Analysis.MatrixDeterminantDerivative

@[expose] public section

/-! # Canonical adjugate spectral projectors and the eigenvalue differential -/
open scoped BigOperators Topology ContDiff
open Matrix Filter
namespace GinibrePoincare
noncomputable section

def matrixScalarCLM (n : ℕ) : ℂ →L[ℂ] GinibreMatrixCoordinates n :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    if i = j then ContinuousLinearMap.id ℂ ℂ else 0

theorem matrixScalarCLM_apply (n : ℕ) (z : ℂ) :
    Matrix.of (matrixScalarCLM n z) = Matrix.scalar (Fin n) z := by
  ext i j
  by_cases h : i = j <;> simp [matrixScalarCLM, Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem matrixScalar_eq_smul_one (n : ℕ) (z : ℂ) :
    Matrix.scalar (Fin n) z = z • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.one_apply]

def matrixCharacteristicLinearMap (n : ℕ) :
    GinibreMatrixCoordinates n × ℂ →L[ℂ] GinibreMatrixCoordinates n :=
  (matrixScalarCLM n).comp (ContinuousLinearMap.snd ℂ _ _) -
    ContinuousLinearMap.fst ℂ _ _

theorem matrixCharacteristicLinearMap_apply (n : ℕ) (p : GinibreMatrixCoordinates n × ℂ) :
    Matrix.of (matrixCharacteristicLinearMap n p) = Matrix.scalar (Fin n) p.2 - Matrix.of p.1 := by
  ext i j
  by_cases h : i = j <;> simp [matrixCharacteristicLinearMap, matrixScalarCLM,
    Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem matrixCharacteristicEquation_hasFDerivAt (n : ℕ) (p : GinibreMatrixCoordinates n × ℂ) :
    HasFDerivAt (matrixCharacteristicEquation n)
      ((matrixDeterminantDerivative n (matrixCharacteristicLinearMap n p)).comp
        (matrixCharacteristicLinearMap n)) p := by
  have h := (matrixDeterminant_hasFDerivAt n (matrixCharacteristicLinearMap n p)).comp p
    (matrixCharacteristicLinearMap n).hasFDerivAt
  convert! h using 1
  funext x
  simp only [Function.comp_def, matrixCharacteristicLinearMap_apply, matrixCharacteristicEquation]

theorem matrixCharacteristicEquation_fderiv_apply (n : ℕ)
    (G H : GinibreMatrixCoordinates n) (z w : ℂ) :
    fderiv ℂ (matrixCharacteristicEquation n) (G, z) (H, w) =
      w * Matrix.trace (Matrix.scalar (Fin n) z - Matrix.of G).adjugate -
        Matrix.trace ((Matrix.scalar (Fin n) z - Matrix.of G).adjugate * Matrix.of H) := by
  rw [(matrixCharacteristicEquation_hasFDerivAt n (G, z)).fderiv]
  simp only [ContinuousLinearMap.comp_apply, matrixDeterminantDerivative_apply,
    matrixCharacteristicLinearMap_apply, Matrix.mul_sub, Matrix.trace_sub]
  rw [matrixScalar_eq_smul_one n w, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul]
  simp [smul_eq_mul]

/-- The scalar characteristic derivative is the trace of the adjugate. -/
theorem matrixCharpoly_derivative_eq_trace_adjugate (n : ℕ)
    (G : GinibreMatrixCoordinates n) (z : ℂ) :
    (Matrix.charpoly (Matrix.of G)).derivative.eval z =
      Matrix.trace (Matrix.scalar (Fin n) z - Matrix.of G).adjugate := by
  have h := congrArg (fun f : ℂ →L[ℂ] ℂ => f 1)
    (matrixCharacteristicEquation_partial_eigenvalue n G z)
  simpa [matrixCharacteristicEquation_fderiv_apply] using h.symm

/-- Canonical simple-root spectral projector, with no choice of eigenvectors. -/
def matrixEigenvalueProjector (n : ℕ) (G : GinibreMatrixCoordinates n) (z : ℂ) :
    Matrix (Fin n) (Fin n) ℂ :=
  ((Matrix.charpoly (Matrix.of G)).derivative.eval z)⁻¹ •
    (Matrix.scalar (Fin n) z - Matrix.of G).adjugate

theorem matrixEigenvalueProjector_trace (n : ℕ) (G : GinibreMatrixCoordinates n) (z : ℂ)
    (hs : (Matrix.charpoly (Matrix.of G)).Separable)
    (hz : (Matrix.charpoly (Matrix.of G)).eval z = 0) :
    Matrix.trace (matrixEigenvalueProjector n G z) = 1 := by
  have hc : (Matrix.charpoly (Matrix.of G)).derivative.eval z ≠ 0 := by
    simpa only [Polynomial.eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) hz
  rw [matrixEigenvalueProjector, Matrix.trace_smul, ← matrixCharpoly_derivative_eq_trace_adjugate]
  simp [smul_eq_mul, hc]

/-- Every differentiable local root branch has the canonical trace differential.
Only the root equation is assumed; its derivative is derived. -/
theorem matrixLocalEigenvalue_fderiv (n : ℕ) (G H : GinibreMatrixCoordinates n) (z : ℂ)
    (hs : (Matrix.charpoly (Matrix.of G)).Separable)
    (hz : (Matrix.charpoly (Matrix.of G)).eval z = 0)
    (eig : GinibreMatrixCoordinates n → ℂ) (hbase : eig G = z)
    (hdiff : DifferentiableAt ℂ eig G)
    (hroot : ∀ᶠ A in 𝓝 G, (Matrix.charpoly (Matrix.of A)).eval (eig A) = 0) :
    fderiv ℂ eig G H = Matrix.trace (matrixEigenvalueProjector n G z * Matrix.of H) := by
  have hc : (Matrix.charpoly (Matrix.of G)).derivative.eval z ≠ 0 := by
    simpa only [Polynomial.eval₂_id] using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) hz
  have hpair := (hasFDerivAt_id G).prodMk hdiff.hasFDerivAt
  have hcomp := ((contDiff_matrixCharacteristicEquation n).differentiable
    (by simp) (G, eig G)).hasFDerivAt.comp G hpair
  have heq : (fun _ : GinibreMatrixCoordinates n => (0 : ℂ)) =ᶠ[𝓝 G]
      (fun A => matrixCharacteristicEquation n (A, eig A)) := by
    filter_upwards [hroot] with A hA
    simpa only [matrixCharacteristicEquation_eq_eval] using hA.symm
  have hzero := (hcomp.congr_of_eventuallyEq heq).unique (hasFDerivAt_const (0 : ℂ) G)
  have hv := congrArg (fun f : GinibreMatrixCoordinates n →L[ℂ] ℂ => f H) hzero
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply, hbase,
    matrixCharacteristicEquation_fderiv_apply] at hv
  rw [← matrixCharpoly_derivative_eq_trace_adjugate] at hv
  rw [matrixEigenvalueProjector, Matrix.smul_mul, Matrix.trace_smul]
  simp only [smul_eq_mul]
  have he := sub_eq_zero.mp hv
  rw [← he]
  field_simp

/-- At every simple eigenvalue there is a complex-smooth eigenvalue branch
with the exact first-order trace perturbation formula in every direction. -/
theorem matrixSimpleSpectrum_exists_local_eigenvalue_with_derivative (n : ℕ)
    (G : GinibreMatrixCoordinates n) (z : ℂ)
    (hs : (Matrix.charpoly (Matrix.of G)).Separable)
    (hz : (Matrix.charpoly (Matrix.of G)).eval z = 0) :
    ∃ eig : GinibreMatrixCoordinates n → ℂ,
      eig G = z ∧ ContDiffAt ℂ ∞ eig G ∧
        (∀ᶠ A in 𝓝 G, (Matrix.charpoly (Matrix.of A)).eval (eig A) = 0) ∧
        ∀ H, fderiv ℂ eig G H = Matrix.trace (matrixEigenvalueProjector n G z * Matrix.of H) := by
  obtain ⟨eig, hb, hd, hr⟩ := matrixSimpleSpectrum_exists_local_eigenvalue n G z hs hz
  refine ⟨eig, hb, hd, hr, fun H => ?_⟩
  exact matrixLocalEigenvalue_fderiv n G H z hs hz eig hb (hd.differentiableAt (by simp)) hr

#print axioms matrixCharpoly_derivative_eq_trace_adjugate
#print axioms matrixEigenvalueProjector_trace
#print axioms matrixSimpleSpectrum_exists_local_eigenvalue_with_derivative

end
end GinibrePoincare
