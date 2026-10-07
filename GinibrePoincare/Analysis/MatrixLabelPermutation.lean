module

public import GinibrePoincare.Analysis.MatrixLocalSpectrum

@[expose] public section

namespace GinibrePoincare
noncomputable section

theorem matrix_injective_full_roots_separable (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (a : Fin n → ℂ) (ha : Function.Injective a)
    (hr : ∀ i, A.charpoly.eval (a i) = 0) : A.charpoly.Separable := by
  classical
  have hsub : Finset.univ.image a ⊆ A.charpoly.roots.toFinset := by
    intro z hz
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hz
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr (hr i))
  have hc : (Finset.univ.image a).card = n := by
    rw [Finset.card_image_of_injective _ ha]
    simp
  have hrootcard : A.charpoly.roots.card = n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  have he : A.charpoly.roots.toFinset.card = A.charpoly.roots.card := by
    have hl := Finset.card_le_card hsub
    have hu := Multiset.toFinset_card_le (m := A.charpoly.roots)
    omega
  exact (Polynomial.nodup_roots_iff_of_splits A.charpoly_monic.ne_zero
    (IsAlgClosed.splits A.charpoly)).mp (Multiset.toFinset_card_eq_card_iff_nodup.mp he)

/-- Any two full labelings of a simple matrix differ by a permutation. -/
theorem matrixSimpleSpectrum_labels_permutation (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hs : A.charpoly.Separable) (a b : Fin n → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hra : ∀ i, A.charpoly.eval (a i) = 0) (hrb : ∀ i, A.charpoly.eval (b i) = 0) :
    ∃ e : Fin n ≃ Fin n, ∀ i, b i = a (e i) := by
  classical
  let s := A.charpoly.roots.toFinset
  have hcard : Fintype.card s = n := by
    rw [Fintype.card_coe]
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hs),
      IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim,
      Fintype.card_fin]
  let fa : Fin n → s := fun i => ⟨a i, Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr (hra i))⟩
  let fb : Fin n → s := fun i => ⟨b i, Multiset.mem_toFinset.mpr
    ((Polynomial.mem_roots A.charpoly_monic.ne_zero).mpr (hrb i))⟩
  have hfa : Function.Bijective fa := (Fintype.bijective_iff_injective_and_card fa).mpr
    ⟨fun i j hij => ha (congrArg Subtype.val hij), by simp [hcard]⟩
  have hfb : Function.Bijective fb := (Fintype.bijective_iff_injective_and_card fb).mpr
    ⟨fun i j hij => hb (congrArg Subtype.val hij), by simp [hcard]⟩
  let ea := Equiv.ofBijective fa hfa
  let eb := Equiv.ofBijective fb hfb
  refine ⟨eb.trans ea.symm, fun i => ?_⟩
  have h := ea.apply_symm_apply (eb i)
  exact (congrArg Subtype.val h).symm

/-- A permutation-invariant observable has an intrinsic value independent of labeling. -/
theorem matrixSimpleSpectrum_symmetric_value (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hs : A.charpoly.Separable) (a b : Fin n → ℂ)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hra : ∀ i, A.charpoly.eval (a i) = 0) (hrb : ∀ i, A.charpoly.eval (b i) = 0)
    (F : (Fin n → ℂ) → ℝ) (hF : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    F a = F b := by
  obtain ⟨e, he⟩ := matrixSimpleSpectrum_labels_permutation n A hs a b ha hb hra hrb
  have hb' : b = a ∘ e := funext he
  rw [hb', hF]

#print axioms matrixSimpleSpectrum_labels_permutation
end
end GinibrePoincare
