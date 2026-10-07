module

public import GinibrePoincare.Analysis.MatrixLabelPermutation
public import Mathlib.Data.Multiset.Fintype

@[expose] public section

/-! # Full spectral configurations including repeated eigenvalues -/
open scoped BigOperators
open Matrix Polynomial
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every complex matrix has an actual complete configuration of roots,
counting multiplicities, including matrices with repeated spectrum. -/
theorem matrix_full_roots_configuration_exists (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ∃ z : Fin n → ℂ, A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (z i)) := by
  classical
  let m := A.charpoly.roots
  have hc : Fintype.card (Fin n) = Fintype.card m := by
    rw [Fintype.card_fin, Multiset.card_coe]
    dsimp [m]
    rw [IsAlgClosed.card_roots_eq_natDegree, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  let e : Fin n ≃ m := Fintype.equivOfCardEq hc
  refine ⟨fun i => (e i : ℂ), ?_⟩
  have he : (m.map (fun z : ℂ => Polynomial.X - Polynomial.C z)).prod =
      ∏ z : m, (Polynomial.X - Polynomial.C (z : ℂ)) := by
    rw [← Multiset.map_univ m (fun z : ℂ => Polynomial.X - Polynomial.C z)]
    rfl
  rw [(IsAlgClosed.splits A.charpoly).eq_prod_roots_of_monic A.charpoly_monic]
  change (m.map (fun z : ℂ => Polynomial.X - Polynomial.C z)).prod = _
  rw [he]
  exact (e.prod_comp (fun z : m => Polynomial.X - Polynomial.C (z : ℂ))).symm

/-- A complete actual eigenvalue configuration, defined also at collisions. -/
def matrixAllEigenvalues (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : Fin n → ℂ :=
  Classical.choose (matrix_full_roots_configuration_exists n A)

theorem matrixAllEigenvalues_charpoly (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (matrixAllEigenvalues n A i)) :=
  Classical.choose_spec (matrix_full_roots_configuration_exists n A)

/-- Full root configurations have exactly the same multiset, with all
multiplicities retained. -/
theorem matrix_full_roots_configuration_multiset {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (z : Fin n → ℂ)
    (hz : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (z i))) :
    (Finset.univ.val.map z) = A.charpoly.roots := by
  rw [hz]
  have hp : (∏ i : Fin n, (Polynomial.X - Polynomial.C (z i))) =
      ((Finset.univ.val.map z).map fun a => Polynomial.X - Polynomial.C a).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hp, Polynomial.roots_multiset_prod_X_sub_C]

/-- Multiplicity-preserving equality of finite configurations yields an
actual particle permutation, without distinctness assumptions. -/
theorem finite_configurations_multiset_permutation {n : ℕ} (a b : Fin n → ℂ)
    (h : Finset.univ.val.map a = Finset.univ.val.map b) :
    ∃ e : Fin n ≃ Fin n, ∀ i, b i = a (e i) := by
  classical
  have hcount (f : Fin n → ℂ) (z : ℂ) :
      Fintype.card {i // f i = z} = (Finset.univ.val.map f).count z := by
    rw [Fintype.card_subtype, Multiset.count_map, ← Finset.filter_val]
    change (Finset.univ.filter fun i => f i = z).card =
      (Finset.univ.filter fun i => z = f i).card
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
  have hc (z : ℂ) : Fintype.card {i // b i = z} = Fintype.card {i // a i = z} := by
    rw [hcount, hcount, h]
  let ef (z : ℂ) : {i // b i = z} ≃ {i // a i = z} := Fintype.equivOfCardEq (hc z)
  let e : Fin n ≃ Fin n := (Equiv.sigmaFiberEquiv b).symm.trans
    ((Equiv.sigmaCongrRight ef).trans (Equiv.sigmaFiberEquiv a))
  refine ⟨e, ?_⟩
  intro i
  exact (ef (b i) ⟨i, rfl⟩).property.symm

/-- Symmetric observables are intrinsic also at repeated matrix spectra. -/
theorem matrix_full_roots_symmetric_value {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (a b : Fin n → ℂ)
    (ha : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (a i)))
    (hb : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (b i)))
    (F : (Fin n → ℂ) → ℝ) (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    F a = F b := by
  obtain ⟨e, he⟩ := finite_configurations_multiset_permutation a b
    ((matrix_full_roots_configuration_multiset A a ha).trans
      (matrix_full_roots_configuration_multiset A b hb).symm)
  have hb' : b = a ∘ e := funext he
  rw [hb', hsym]

/-- The actual symmetric spectral value defined on all complex matrices. -/
def matrixFullSymmetricSpectralLift (n : ℕ) (F : (Fin n → ℂ) → ℝ) :
    Matrix (Fin n) (Fin n) ℂ → ℝ := fun A => F (matrixAllEigenvalues n A)

end
end GinibrePoincare
