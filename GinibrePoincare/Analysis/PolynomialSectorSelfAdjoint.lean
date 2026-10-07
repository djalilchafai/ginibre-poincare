module

public import GinibrePoincare.Analysis.PolynomialSectorGenerator

@[expose] public section

/-! # Self-adjointness of the genuine closed polynomial-sector generator -/
open scoped LinearPMap
namespace GinibrePoincare
noncomputable section

/-- Actual sector eigenvectors belong to the exact closed generator graph. -/
theorem polynomialSectorGenerator_eigenpair (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    (polynomialSectorHilbertBasis n hn i,
      -(eigenvalue n i.a i.b i.m : ℂ) • polynomialSectorHilbertBasis n hn i) ∈
      (polynomialSectorGenerator n hn).graph := by
  classical
  rw [polynomialSectorGenerator_graph]
  intro j
  have hb := (polynomialSectorHilbertBasis n hn).orthonormal
  have he := (orthonormal_iff_ite.mp hb) j i
  have hmul : inner ℂ (polynomialSectorHilbertBasis n hn j)
      (-(eigenvalue n i.a i.b i.m : ℂ) • polynomialSectorHilbertBasis n hn i) =
      -(eigenvalue n i.a i.b i.m : ℂ) *
        inner ℂ (polynomialSectorHilbertBasis n hn j) (polynomialSectorHilbertBasis n hn i) := by
    change inner ℂ (polynomialSectorHilbertBasis n hn j : GinibrePolynomialL2 n)
      (-(eigenvalue n i.a i.b i.m : ℂ) •
        (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)) = _
    exact inner_smul_right _ _ _
  rw [hmul, he]
  by_cases hji : j = i
  · subst j
    rfl
  · simp only [hji, if_false, mul_zero]

/-- The exact sector generator has dense domain. -/
theorem polynomialSectorGenerator_dense_domain (n : ℕ) (hn : 2 ≤ n) :
    Dense ((polynomialSectorGenerator n hn).domain : Set (closedPolynomialSector n hn)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  apply top_unique
  rw [← (polynomialSectorHilbertBasis n hn).dense_span]
  apply Submodule.topologicalClosure_mono
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact LinearPMap.mem_domain_of_mem_graph (polynomialSectorGenerator_eigenpair n hn i)

/-- Actual sector graph symmetry, inherited from its identified Ginibre L² closure. -/
theorem polynomialSectorGenerator_graph_symmetric (n : ℕ) (hn : 2 ≤ n)
    (p q : closedPolynomialSector n hn × closedPolynomialSector n hn)
    (hp : p ∈ (polynomialSectorGenerator n hn).graph)
    (hq : q ∈ (polynomialSectorGenerator n hn).graph) :
    inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
  exact closedPolynomialGenerator_graph_symmetric n hn
    ((p.1 : GinibrePolynomialL2 n), (p.2 : GinibrePolynomialL2 n))
    ((q.1 : GinibrePolynomialL2 n), (q.2 : GinibrePolynomialL2 n))
    ((polynomialSectorGenerator_graph_iff_ambient n hn p.1 p.2).mp hp)
    ((polynomialSectorGenerator_graph_iff_ambient n hn q.1 q.2).mp hq)

/-- Maximality of the symmetric graph, proved by testing the adjoint against
all actual eigenvectors rather than assuming essential self-adjointness. -/
theorem polynomialSectorGenerator_graph_adjoint (n : ℕ) (hn : 2 ≤ n) :
    (polynomialSectorGenerator n hn).graph.adjoint =
      (polynomialSectorGenerator n hn).graph := by
  ext p
  rw [Submodule.mem_adjoint_iff]
  constructor
  · intro hp
    rw [polynomialSectorGenerator_graph]
    intro i
    have h := hp (polynomialSectorHilbertBasis n hn i)
      (-(eigenvalue n i.a i.b i.m : ℂ) • polynomialSectorHilbertBasis n hn i)
      (polynomialSectorGenerator_eigenpair n hn i)
    change inner ℂ (-(eigenvalue n i.a i.b i.m : ℂ) •
      (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n))
      (p.1 : GinibrePolynomialL2 n) -
      inner ℂ (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)
        (p.2 : GinibrePolynomialL2 n) = 0 at h
    rw [inner_smul_left] at h
    simp only [map_neg, Complex.conj_ofReal] at h
    exact (sub_eq_zero.mp h).symm
  · intro hp a b hab
    exact sub_eq_zero.mpr (polynomialSectorGenerator_graph_symmetric n hn (a, b) p hab hp)

/-- Self-adjointness in the actual complete Ginibre L² polynomial sector. -/
theorem polynomialSectorGenerator_selfAdjoint (n : ℕ) (hn : 2 ≤ n) :
    IsSelfAdjoint (polynomialSectorGenerator n hn) := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (polynomialSectorGenerator_dense_domain n hn),
    polynomialSectorGenerator_graph_adjoint]

/-- The maximal spectral generator is closed. -/
theorem polynomialSectorGenerator_isClosed (n : ℕ) (hn : 2 ≤ n) :
    (polynomialSectorGenerator n hn).IsClosed :=
  (polynomialSectorGenerator_selfAdjoint n hn).isClosed

end
end GinibrePoincare
