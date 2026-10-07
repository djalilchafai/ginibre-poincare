module

public import GinibrePoincare.Analysis.MatrixSpectralLiftDifferential

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

def realDifferentialWirtinger {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℝ) (i : Fin n) : ℂ :=
  ((L (Pi.single i 1) : ℂ) - Complex.I * (L (Pi.single i Complex.I) : ℂ)) / 2

/-- Every actual real differential on complex coordinates has the Wirtinger decomposition. -/
theorem realDifferentialWirtinger_apply {n : ℕ} (L : (Fin n → ℂ) →L[ℝ] ℝ)
    (z : Fin n → ℂ) : L z = 2 * (∑ i, realDifferentialWirtinger L i * z i).re := by
  classical
  have hz : z = ∑ i : Fin n,
      ((z i).re • (Pi.single i 1 : Fin n → ℂ) +
        (z i).im • (Pi.single i Complex.I : Fin n → ℂ)) := by
    ext j
    simp [Pi.single_apply, Complex.real_smul, Finset.sum_add_distrib, eq_comm]
  conv_lhs => rw [hz, map_sum]
  simp only [map_add, map_smul, smul_eq_mul, Complex.re_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [realDifferentialWirtinger, Complex.div_re, Complex.normSq_apply,
    Complex.mul_re, Complex.mul_im]
  ring

theorem matrixLocalSpectralLift_wirtinger (n : ℕ) (A H : GinibreMatrixCoordinates n)
    (labels : GinibreMatrixCoordinates n → Fin n → ℂ) (F : (Fin n → ℂ) → ℝ)
    (hs : (Matrix.of A).charpoly.Separable) (hd : DifferentiableAt ℂ labels A)
    (hF : DifferentiableAt ℝ F (labels A))
    (hr : ∀ᶠ B in nhds A, ∀ i, (Matrix.of B).charpoly.eval (labels B i) = 0) :
    fderiv ℝ (F ∘ labels) A H =
      2 * (∑ i, realDifferentialWirtinger (fderiv ℝ F (labels A)) i *
        Matrix.trace (matrixEigenvalueProjector n A (labels A i) * Matrix.of H)).re := by
  rw [matrixLocalSpectralLift_fderiv n A H labels F hs hd hF hr]
  exact realDifferentialWirtinger_apply _ _

#print axioms realDifferentialWirtinger_apply
#print axioms matrixLocalSpectralLift_wirtinger
end
end GinibrePoincare
