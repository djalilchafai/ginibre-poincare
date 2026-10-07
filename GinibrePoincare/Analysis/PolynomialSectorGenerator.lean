module

public import GinibrePoincare.Analysis.PolynomialSectorHilbertBasis
public import Mathlib.Analysis.InnerProductSpace.LinearPMap

@[expose] public section

/-! # Exact spectral domain of the closed polynomial generator -/
open Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Spectral graph on the actual complete sum/radius sector. -/
def polynomialSectorSpectralGraph (n : ℕ) (hn : 2 ≤ n) :
    Submodule ℂ (closedPolynomialSector n hn × closedPolynomialSector n hn) where
  carrier := {p | ∀ i, inner ℂ (polynomialSectorHilbertBasis n hn i) p.2 =
    -(eigenvalue n i.a i.b i.m : ℂ) * inner ℂ (polynomialSectorHilbertBasis n hn i) p.1}
  zero_mem' := by simp
  add_mem' := by
    intro p q hp hq i
    change inner ℂ _ (p.2 + q.2) = _ * inner ℂ _ (p.1 + q.1)
    rw [inner_add_right, inner_add_right, hp i, hq i, mul_add]
  smul_mem' := by
    intro c p hp i
    change inner ℂ (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)
      (c • (p.2 : GinibrePolynomialL2 n)) =
      -(eigenvalue n i.a i.b i.m : ℂ) *
        inner ℂ (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)
          (c • (p.1 : GinibrePolynomialL2 n))
    have hpi := hp i
    change inner ℂ (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)
      (p.2 : GinibrePolynomialL2 n) =
      -(eigenvalue n i.a i.b i.m : ℂ) *
        inner ℂ (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)
          (p.1 : GinibrePolynomialL2 n) at hpi
    rw [inner_smul_right, inner_smul_right, hpi]
    ring

/-- Spectral equations determine the generator output uniquely. -/
theorem polynomialSectorSpectralGraph_singleValued (n : ℕ) (hn : 2 ≤ n)
    (p : closedPolynomialSector n hn × closedPolynomialSector n hn)
    (hp : p ∈ polynomialSectorSpectralGraph n hn) (hx : p.1 = 0) : p.2 = 0 := by
  apply (polynomialSectorHilbertBasis n hn).repr.injective
  apply lp.ext
  funext i
  rw [HilbertBasis.repr_apply_apply, HilbertBasis.repr_apply_apply]
  simpa only [hx, inner_zero_right, mul_zero] using hp i

/-- The graph-defined closed-sector generator. -/
def polynomialSectorGenerator (n : ℕ) (hn : 2 ≤ n) :
    closedPolynomialSector n hn →ₗ.[ℂ] closedPolynomialSector n hn :=
  (polynomialSectorSpectralGraph n hn).toLinearPMap

theorem polynomialSectorGenerator_graph (n : ℕ) (hn : 2 ≤ n) :
    (polynomialSectorGenerator n hn).graph = polynomialSectorSpectralGraph n hn :=
  Submodule.toLinearPMap_graph_eq _ (polynomialSectorSpectralGraph_singleValued n hn)

private theorem polynomialSectorBasisPair_mem_ambient_graph (n : ℕ) (hn : 2 ≤ n)
    (i : PolynomialEigenfunctionData n) :
    ((polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n),
      -(eigenvalue n i.a i.b i.m : ℂ) •
        (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n)) ∈
      (closedPolynomialGenerator n hn).graph := by
  have h := (closedPolynomialGenerator n hn).graph.smul_mem
    (‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ)
    (polynomialEigenfunction_mem_closedGenerator_graph n hn i)
  simp only [polynomialSectorHilbertBasis_apply]
  change ((‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialEigenfunctionL2 n hn i,
    -(eigenvalue n i.a i.b i.m : ℂ) •
      ((‖polynomialSectorEigenvector n hn i‖⁻¹ : ℂ) • polynomialEigenfunctionL2 n hn i)) ∈
      (closedPolynomialGenerator n hn).graph
  rw [smul_comm (-(eigenvalue n i.a i.b i.m : ℂ))]
  exact h

/-- Membership in the original actual L² graph closure implies all spectral equations. -/
theorem polynomialSectorGenerator_spectral_of_ambient_graph (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn)
    (hp : ((u : GinibrePolynomialL2 n), (v : GinibrePolynomialL2 n)) ∈
      (closedPolynomialGenerator n hn).graph) :
    (u, v) ∈ polynomialSectorSpectralGraph n hn := by
  intro i
  have h := closedPolynomialGenerator_graph_symmetric n hn
    ((polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n),
      -(eigenvalue n i.a i.b i.m : ℂ) •
        (polynomialSectorHilbertBasis n hn i : GinibrePolynomialL2 n))
    ((u : GinibrePolynomialL2 n), (v : GinibrePolynomialL2 n))
    (polynomialSectorBasisPair_mem_ambient_graph n hn i) hp
  simp only [inner_smul_left, map_neg, Complex.conj_ofReal] at h
  exact h.symm

/-- The spectral equations suffice for membership in the original graph closure.
The proof sums the actual Hilbert-basis eigenpairs in the product L² topology. -/
theorem polynomialSectorGenerator_ambient_graph_of_spectral (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn)
    (hp : (u, v) ∈ polynomialSectorSpectralGraph n hn) :
    ((u : GinibrePolynomialL2 n), (v : GinibrePolynomialL2 n)) ∈
      (closedPolynomialGenerator n hn).graph := by
  let b := polynomialSectorHilbertBasis n hn
  let embed : (closedPolynomialSector n hn × closedPolynomialSector n hn) →L[ℂ]
      (GinibrePolynomialL2 n × GinibrePolynomialL2 n) :=
    (closedPolynomialSector n hn).subtypeL.prodMap (closedPolynomialSector n hn).subtypeL
  have hs := (b.hasSum_repr u).prodMk (b.hasSum_repr v)
  have he := embed.hasSum hs
  have hc := closedPolynomialGenerator_isClosed n hn
  apply hc.mem_of_tendsto he
  apply Eventually.of_forall
  intro s
  apply Submodule.sum_mem
  intro i hi
  have hcoeff : b.repr v i = -(eigenvalue n i.a i.b i.m : ℂ) * b.repr u i := by
    simpa only [HilbertBasis.repr_apply_apply] using hp i
  have hm := (closedPolynomialGenerator n hn).graph.smul_mem (b.repr u i)
    (polynomialSectorBasisPair_mem_ambient_graph n hn i)
  change ((b.repr u i) • (b i : GinibrePolynomialL2 n),
    (b.repr v i) • (b i : GinibrePolynomialL2 n)) ∈ _
  rw [hcoeff, mul_smul, smul_comm (-(eigenvalue n i.a i.b i.m : ℂ))]
  exact hm

/-- Exact identification with the previously constructed concrete graph closure. -/
theorem polynomialSectorGenerator_graph_iff_ambient (n : ℕ) (hn : 2 ≤ n)
    (u v : closedPolynomialSector n hn) :
    (u, v) ∈ (polynomialSectorGenerator n hn).graph ↔
      ((u : GinibrePolynomialL2 n), (v : GinibrePolynomialL2 n)) ∈
        (closedPolynomialGenerator n hn).graph := by
  rw [polynomialSectorGenerator_graph]
  exact ⟨polynomialSectorGenerator_ambient_graph_of_spectral n hn u v,
    polynomialSectorGenerator_spectral_of_ambient_graph n hn u v⟩

end
end GinibrePoincare
