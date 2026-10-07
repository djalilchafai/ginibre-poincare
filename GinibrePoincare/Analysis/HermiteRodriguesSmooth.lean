module

public import GinibrePoincare.Analysis.HermiteRodriguesNormalization

@[expose] public section
open scoped ContDiff ComplexConjugate
namespace GinibrePoincare
namespace ComplexHermite
noncomputable section

theorem rodrigues_contDiff_diagonal (P : Poly) :
    ContDiff ℝ ∞ (diagonalEvalPublic P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    convert! (contDiff_const : ContDiff ℝ ∞ (fun _ : ℂ => a)) using 1
    funext z
    simp [diagonalEvalPublic]
  | add P Q hP hQ =>
    convert! hP.add hQ using 1
    all_goals funext z; simp [diagonalEvalPublic]
  | mul_X P i hP =>
    have hi : ContDiff ℝ ∞ (fun z : ℂ => (![z,conj z] : Fin 2 → ℂ) i) := by
      fin_cases i
      · exact contDiff_id
      · exact Complex.conjCLE.contDiff
    convert! hP.mul hi using 1
    all_goals funext z; simp [diagonalEvalPublic]

theorem contDiff_iterate_dhol_gaussian (n q : ℕ) :
    ContDiff ℝ ∞ (dholOne^[q] (rodriguesGaussian n)) := by
  rw [iterate_dholOne_rodriguesGaussian]
  exact (contDiff_const.mul (Complex.conjCLE.contDiff.pow q)).mul (contDiff_rodriguesGaussian n)

theorem contDiff_iterate_mixed_gaussian (n : ℕ) (hn : 0<n) (p q : ℕ) :
    ContDiff ℝ ∞ (dbarOnePublic^[p] (dholOne^[q] (rodriguesGaussian n))) := by
  rw [iterate_wirtinger_rodrigues_raw n hn]
  exact (contDiff_const.mul (rodrigues_contDiff_diagonal (raw ((n:ℝ)⁻¹) p q))).mul
    (contDiff_rodriguesGaussian n)

end
end ComplexHermite
end GinibrePoincare
