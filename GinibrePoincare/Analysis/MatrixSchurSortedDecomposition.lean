module

public import GinibrePoincare.Analysis.MatrixSchurDiagonal
public import Mathlib.Data.Finset.Sort

@[expose] public section

open Matrix InnerProductSpace Order
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem matrixEigenvalues_sorted_permutation (n : ℕ) (a : Fin n → ℂ)
    (ha : Function.Injective a) :
    ∃ e : Fin n ≃ Fin n, StrictMono (fun i => toLex ((a (e i)).re, (a (e i)).im)) := by
  classical
  let v : Fin n → ℝ ×ₗ ℝ := fun i => toLex ((a i).re, (a i).im)
  have hv : Function.Injective v := by
    intro i j hij
    apply ha
    apply Complex.ext
    · exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).1) hij
    · exact congrArg (fun p : ℝ ×ₗ ℝ => (ofLex p).2) hij
  let s := Finset.univ.image v
  have hc : s.card = n := by
    rw [Finset.card_image_of_injective _ hv]
    simp
  let f : Fin n → s := fun i => ⟨v i, Finset.mem_image_of_mem v (Finset.mem_univ i)⟩
  have hf : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨fun i j hij => hv (congrArg Subtype.val hij), by simp [hc]⟩
  let e0 := Equiv.ofBijective f hf
  let o := s.orderIsoOfFin hc
  let e := o.toEquiv.trans e0.symm
  have he (i : Fin n) : v (e i) = (o i).val := by
    have hh := e0.apply_symm_apply (o i)
    exact congrArg Subtype.val hh
  refine ⟨e, ?_⟩
  intro i j hij
  change v (e i) < v (e j)
  rw [he, he]
  exact o.strictMono hij

/-- Every simple matrix has a unitary Schur representation with lexicographically
ordered distinct diagonal, rather than an unspecified permutation of its spectrum. -/
theorem matrixSimpleSpectrum_exists_sorted_unitary_schur (n : ℕ)
    (G : Matrix (Fin n) (Fin n) ℂ) (hs : G.charpoly.Separable) :
    ∃ Q T : Matrix (Fin n) (Fin n) ℂ,
      Q ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ (∀ i j, j < i → T i j = 0) ∧
      matrixSchurOrderedDiagonal T ∧ G = Q * T * Qᴴ := by
  classical
  obtain ⟨eig, b, hi, hb⟩ := matrixSimpleSpectrum_exists_eigenbasis n G hs
  obtain ⟨p, hp⟩ := matrixEigenvalues_sorted_permutation n eig hi
  let c := b.reindex p.symm
  let eig' : Fin n → ℂ := eig ∘ p
  have hc (i : Fin n) : G *ᵥ c i = eig' i • c i := by
    simpa [c, eig'] using hb (p i)
  let e := WithLp.linearEquiv 2 ℂ (Fin n → ℂ)
  let f := e.symm.toLinearMap.comp (G.toLin'.comp e.toLinearMap)
  let b' := c.map e.symm
  have hb' (i : Fin n) : f (b' i) = eig' i • b' i := by
    change e.symm (G *ᵥ e (e.symm (c i))) = eig' i • e.symm (c i)
    rw [e.apply_symm_apply, hc i, map_smul]
  let s := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨Q, T, hQ, hT, hdiag, he⟩ := eigenbasis_exists_unitary_schur_with_diagonal n f b' eig' hb' s
  have hmat : LinearMap.toMatrix s.toBasis s.toBasis f = G := by
    ext i j
    simp [LinearMap.toMatrix_apply, s, f, e, EuclideanSpace.basisFun_apply,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      Matrix.toLin'_apply, Matrix.mulVec, dotProduct, EuclideanSpace.single_apply]
  refine ⟨Q, T, hQ, hT, ?_, hmat ▸ he⟩
  intro i j hij
  change toLex ((T i i).re, (T i i).im) < toLex ((T j j).re, (T j j).im)
  rw [hdiag, hdiag]
  exact hp hij

#print axioms matrixSimpleSpectrum_exists_sorted_unitary_schur
end
end GinibrePoincare
