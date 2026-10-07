module

public import GinibrePoincare.Analysis.PolynomialSectorSemigroup
public import GinibrePoincare.Analysis.PolynomialGeneratorKernel
public import Mathlib.Analysis.InnerProductSpace.l2Space

@[expose] public section

/-! # Complete normalized Hermite–Laguerre basis of the concrete closed sector -/
namespace GinibrePoincare
noncomputable section

/-- No actual equilibrium Hermite–Laguerre vector is zero. -/
theorem polynomialSectorEigenvector_ne_zero (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) : polynomialSectorEigenvector n hn i ≠ 0 := by
  intro h
  have hz : polynomialEigenfunctionL2 n hn i = 0 := congrArg Subtype.val h
  have hi := polynomialEigenfunction_inner_self_ne_zero n hn i
  rw [← inner_polynomialEigenfunctionL2 n hn i i, hz] at hi
  simp at hi

/-- Normalization in the actual equilibrium L² norm. -/
def normalizedPolynomialSectorEigenvector (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) : closedPolynomialSector n hn :=
  (‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialSectorEigenvector n hn i

theorem normalizedPolynomialSectorEigenvector_orthonormal (n : ℕ) (hn : 2 ≤ n) :
    Orthonormal ℂ (normalizedPolynomialSectorEigenvector n hn) := by
  constructor
  · intro i
    exact norm_smul_inv_norm (polynomialSectorEigenvector_ne_zero n hn i)
  · intro i j hij
    change inner ℂ
      ((‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialEigenfunctionL2 n hn i)
      ((‖polynomialSectorEigenvector n hn j‖⁻¹ : ℂ) • polynomialEigenfunctionL2 n hn j) = 0
    rw [inner_smul_left (𝕜 := ℂ), inner_smul_right (𝕜 := ℂ)]
    have ho : inner ℂ (polynomialEigenfunctionL2 n hn i)
        (polynomialEigenfunctionL2 n hn j) = 0 := by
      rw [inner_polynomialEigenfunctionL2]
      apply polynomialEigenfunction_equilibrium_orthogonal n hn
      rintro ⟨ha, hb, hm⟩
      apply hij
      cases i
      cases j
      simp_all
    rw [ho, mul_zero, mul_zero]

/-- The normalization does not change the algebraic span. -/
theorem polynomialSectorEigenvector_mem_normalized_span (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    polynomialSectorEigenvector n hn i ∈ Submodule.span ℂ
      (Set.range (normalizedPolynomialSectorEigenvector n hn)) := by
  have hnorm : ‖polynomialSectorEigenvector n hn i‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (polynomialSectorEigenvector_ne_zero n hn i)
  have h := (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n hn))).smul_mem
    (‖polynomialSectorEigenvector n hn i‖ : ℂ) (Submodule.subset_span ⟨i, rfl⟩)
  simpa only [normalizedPolynomialSectorEigenvector, smul_smul,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hnorm), one_smul] using h

/-- Completeness in the actual closed sector. -/
theorem normalizedPolynomialSectorEigenvector_dense_span (n : ℕ) (hn : 2 ≤ n) :
    (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n hn))).topologicalClosure = ⊤ := by
  apply top_unique
  intro x hx
  refine (polynomialSectorCombination_dense n hn).induction_on x ?_ ?_
  · exact (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n hn))).isClosed_topologicalClosure
  · intro c
    apply (Submodule.span ℂ (Set.range (normalizedPolynomialSectorEigenvector n hn))).le_topologicalClosure
    unfold polynomialSectorCombination
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (polynomialSectorEigenvector_mem_normalized_span n hn i)

/-- The concrete closed polynomial-sector Hilbert basis. -/
def polynomialSectorHilbertBasis (n : ℕ) (hn : 2 ≤ n) :
    HilbertBasis (PolynomialEigenfunctionData n) ℂ (closedPolynomialSector n hn) :=
  HilbertBasis.mk (normalizedPolynomialSectorEigenvector_orthonormal n hn)
    (by rw [normalizedPolynomialSectorEigenvector_dense_span])

@[simp] theorem polynomialSectorHilbertBasis_apply (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    polynomialSectorHilbertBasis n hn i = normalizedPolynomialSectorEigenvector n hn i := by
  simp [polynomialSectorHilbertBasis]

end
end GinibrePoincare
