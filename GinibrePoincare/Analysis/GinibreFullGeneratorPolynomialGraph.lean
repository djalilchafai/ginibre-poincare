module

public import GinibrePoincare.Analysis.GinibreFullGeneratorPolynomialCompatibility
public import GinibrePoincare.Analysis.PolynomialSectorGenerator

@[expose] public section

noncomputable section
namespace GinibrePoincare
open Filter
set_option backward.isDefEq.respectTransparency false

lemma ginibreFullGenerator_polynomial_basis_graph (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    (ginibreFullPolynomialSectorInclusion n hn (polynomialSectorHilbertBasis n hn i),
      -(eigenvalue n i.a i.b i.m : ℂ) •
        ginibreFullPolynomialSectorInclusion n hn (polynomialSectorHilbertBasis n hn i)) ∈
      (ginibreFullGenerator n (by omega)).graph := by
  have hg := ginibreFullGenerator_polynomial_eigenvector n hn i
  have hg' : (ginibreFullPolynomialEigenvector n hn i,
      -(eigenvalue n i.a i.b i.m : ℂ) • ginibreFullPolynomialEigenvector n hn i) ∈
      (ginibreFullGenerator n (by omega)).graph := by
    have hs : -(eigenvalue n i.a i.b i.m : ℂ) • ginibreFullPolynomialEigenvector n hn i =
        -(eigenvalue n i.a i.b i.m : ℝ) • ginibreFullPolynomialEigenvector n hn i := by
      rw [← algebraMap_smul ℂ (-(eigenvalue n i.a i.b i.m : ℝ))]
      simp only [map_neg]
      rfl
    rw [hs]
    exact hg
  have h := (ginibreFullGenerator n (by omega)).graph.smul_mem
    (‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) hg'
  rw [polynomialSectorHilbertBasis_apply]
  change (ginibreFullPolynomialSectorInclusion n hn
      ((‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialSectorEigenvector n hn i),
    -(eigenvalue n i.a i.b i.m : ℂ) • ginibreFullPolynomialSectorInclusion n hn
      ((‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialSectorEigenvector n hn i)) ∈ _
  rw [map_smul, ginibreFullPolynomialSectorInclusion_eigenvector,
    smul_comm (-(eigenvalue n i.a i.b i.m : ℂ))]
  exact h

/-- The maximal full weak generator restricted to the closed polynomial sector
is exactly the independently closed spectral polynomial generator. -/
theorem ginibreFullGenerator_polynomial_graph_iff (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn) :
    (ginibreFullPolynomialSectorInclusion n hn u, ginibreFullPolynomialSectorInclusion n hn v) ∈
        (ginibreFullGenerator n (by omega)).graph ↔
      (u, v) ∈ (polynomialSectorGenerator n hn).graph := by
  rw [polynomialSectorGenerator_graph]
  constructor
  · intro hp i
    have hg := ginibreFullGenerator_polynomial_basis_graph n hn i
    rw [ginibreFullGenerator, resolventGenerator_graph _ (ginibreFullComplexResolvent_injective n (by omega))] at hg hp
    have h := resolventGeneratorGraph_symmetric (ginibreFullComplexResolvent n (by omega))
      (ginibreFullComplexResolvent_isSelfAdjoint n (by omega))
      (ginibreFullPolynomialSectorInclusion n hn (polynomialSectorHilbertBasis n hn i),
        -(eigenvalue n i.a i.b i.m : ℂ) •
          ginibreFullPolynomialSectorInclusion n hn (polynomialSectorHilbertBasis n hn i))
      (ginibreFullPolynomialSectorInclusion n hn u, ginibreFullPolynomialSectorInclusion n hn v)
      hg hp
    simp only [Prod.fst, Prod.snd] at h
    rw [inner_smul_left
      (ginibreFullPolynomialSectorInclusion n hn (polynomialSectorHilbertBasis n hn i))
      (ginibreFullPolynomialSectorInclusion n hn u) (-(eigenvalue n i.a i.b i.m : ℂ))] at h
    simp only [map_neg, Complex.conj_ofReal] at h
    exact h.symm
  · intro hp
    let b := polynomialSectorHilbertBasis n hn
    let embed := (ginibreFullPolynomialSectorInclusion n hn).prodMap
      (ginibreFullPolynomialSectorInclusion n hn)
    have hs := (b.hasSum_repr u).prodMk (b.hasSum_repr v)
    have he := embed.hasSum hs
    have hc := ginibreFullGenerator_isClosed n (by omega)
    apply hc.mem_of_tendsto he
    apply Eventually.of_forall
    intro s
    apply Submodule.sum_mem
    intro i hi
    have hcoeff : b.repr v i = -(eigenvalue n i.a i.b i.m : ℂ) * b.repr u i := by
      simpa only [HilbertBasis.repr_apply_apply] using hp i
    have hm := (ginibreFullGenerator n (by omega)).graph.smul_mem (b.repr u i)
      (ginibreFullGenerator_polynomial_basis_graph n hn i)
    change ((b.repr u i) • ginibreFullPolynomialSectorInclusion n hn (b i),
      (b.repr v i) • ginibreFullPolynomialSectorInclusion n hn (b i)) ∈ _
    rw [hcoeff, mul_smul, smul_comm (-(eigenvalue n i.a i.b i.m : ℂ))]
    exact hm

end GinibrePoincare
