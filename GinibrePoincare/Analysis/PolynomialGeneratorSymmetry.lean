module

public import GinibrePoincare.Analysis.PolynomialGeneratorClosure

@[expose] public section

/-! # Symmetry of the closed polynomial-sector generator

Symmetry is proved in the actual Ginibre L² scalar product and passes to the
actual graph closure. Self-adjointness and full diffusion identification are
not consequences asserted here.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

private theorem polynomialGeneratorGraph_symmetry (n : ℕ) (hn : 2 ≤ n)
    (p q : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ polynomialGeneratorGraph n hn)
    (hq : q ∈ polynomialGeneratorGraph n hn) :
    inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨i, rfl⟩ := hp
    induction hq using Submodule.span_induction with
    | mem q hq =>
      obtain ⟨j, rfl⟩ := hq
      change inner ℂ (-(eigenvalue n i.a i.b i.m : ℂ) • _) _ =
        inner ℂ _ (-(eigenvalue n j.a j.b j.m : ℂ) • _)
      rw [inner_smul_left, inner_smul_right]
      by_cases hij : i = j
      · subst j
        simp
      · have ho : inner ℂ (polynomialEigenfunctionL2 n hn i)
            (polynomialEigenfunctionL2 n hn j) = 0 := by
          rw [inner_polynomialEigenfunctionL2]
          apply polynomialEigenfunction_equilibrium_orthogonal n hn
          rintro ⟨ha, hb, hm⟩
          apply hij
          cases i
          cases j
          simp_all
        simp [ho]
    | zero => simp
    | add x y _ _ hx hy => simp_all [inner_add_right]
    | smul c x _ hx => simp_all [inner_smul_right]
  | zero => simp
  | add x y _ _ hx hy => simp_all [inner_add_left]
  | smul c x _ hx => simp_all [inner_smul_left]

/-- The graph-closed polynomial realization is symmetric in actual Ginibre L². -/
theorem closedPolynomialGenerator_graph_symmetric (n : ℕ) (hn : 2 ≤ n)
    (p q : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
    (hp : p ∈ (closedPolynomialGenerator n hn).graph)
    (hq : q ∈ (closedPolynomialGenerator n hn).graph) :
    inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
  rw [closedPolynomialGenerator_graph] at hp hq
  have hfinite (q : GinibrePolynomialL2 n × GinibrePolynomialL2 n)
      (hq : q ∈ polynomialGeneratorGraph n hn) :
      inner ℂ p.2 q.1 = inner ℂ p.1 q.2 := by
    have hc : IsClosed {p : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
        inner ℂ p.2 q.1 = inner ℂ p.1 q.2} := by
      apply isClosed_eq <;> fun_prop
    exact closure_minimal (fun p hp => polynomialGeneratorGraph_symmetry n hn p q hp hq)
      hc hp
  have hc : IsClosed {q : GinibrePolynomialL2 n × GinibrePolynomialL2 n |
      inner ℂ p.2 q.1 = inner ℂ p.1 q.2} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal hfinite hc hq

/-- Domain-valued symmetry for the closed partial linear operator. -/
theorem closedPolynomialGenerator_symmetric (n : ℕ) (hn : 2 ≤ n)
    (u v : (closedPolynomialGenerator n hn).domain) :
    inner ℂ ((closedPolynomialGenerator n hn) u) v.1 =
      inner ℂ u.1 ((closedPolynomialGenerator n hn) v) := by
  apply closedPolynomialGenerator_graph_symmetric n hn
    (u.1, (closedPolynomialGenerator n hn) u)
    (v.1, (closedPolynomialGenerator n hn) v)
  · exact (LinearPMap.image_iff u.2).mp rfl
  · exact (LinearPMap.image_iff v.2).mp rfl

end
end GinibrePoincare
