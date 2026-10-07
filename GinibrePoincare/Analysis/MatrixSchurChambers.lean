module

public import GinibrePoincare.Analysis.MatrixSchurOrderedSpectralLaw

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

theorem matrixSchurOrderedConfigurations_iff {n : ℕ} (z : Fin n → ℂ) :
    z ∈ matrixSchurOrderedConfigurations n ↔
      StrictMono (fun i => toLex ((z i).re, (z i).im)) := by
  unfold matrixSchurOrderedConfigurations matrixSchurOrderedDiagonal
  simp only [Set.mem_setOf_eq, Matrix.diagonal_apply_eq]

theorem matrixSchurOrderedConfigurations_injective {n : ℕ} (z : Fin n → ℂ)
    (hz : z ∈ matrixSchurOrderedConfigurations n) : Function.Injective z := by
  have hi := ((matrixSchurOrderedConfigurations_iff z).mp hz).injective
  intro i j hij
  apply hi
  exact congrArg (fun w : ℂ => toLex (w.re, w.im)) hij

def matrixSchurPermutationChamber {n : ℕ} (e : Fin n ≃ Fin n) : Set (Fin n → ℂ) :=
  {z | z ∘ e ∈ matrixSchurOrderedConfigurations n}

theorem measurableSet_matrixSchurPermutationChamber {n : ℕ} (e : Fin n ≃ Fin n) :
    MeasurableSet (matrixSchurPermutationChamber e) :=
  (measurableSet_matrixSchurOrderedConfigurations n).preimage (by fun_prop)

theorem matrixSchurPermutationChamber_pairwise_disjoint (n : ℕ) :
    Pairwise (fun e f : Fin n ≃ Fin n => Disjoint (matrixSchurPermutationChamber e)
      (matrixSchurPermutationChamber f)) := by
  intro e f hne
  apply Set.disjoint_left.mpr
  intro z he hf
  have hme := (matrixSchurOrderedConfigurations_iff (z ∘ e)).mp he
  have hmf := (matrixSchurOrderedConfigurations_iff (z ∘ f)).mp hf
  let a : Fin n → ℝ ×ₗ ℝ := fun i => toLex ((z i).re, (z i).im)
  have hr : Set.range (a ∘ e) = Set.range (a ∘ f) := by
    simp only [Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
  have heq : a ∘ e = a ∘ f := Set.range_injOn_strictMono hme hmf hr
  have hi : Function.Injective a := by
    intro i j hij
    have heinj : Function.Injective (a ∘ e) := hme.injective
    have h : e.symm i = e.symm j := by
      apply heinj
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact e.symm.injective h
  apply hne
  apply Equiv.ext
  intro i
  exact hi (congrFun heq i)

theorem matrixSchurPermutationChamber_cover (n : ℕ) :
    (⋃ e : Fin n ≃ Fin n, matrixSchurPermutationChamber e) =
      {z : Fin n → ℂ | Function.Injective z} := by
  ext z
  constructor
  · intro hz
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hz
    have hi := matrixSchurOrderedConfigurations_injective (z ∘ e) he
    intro i j hij
    have h : e.symm i = e.symm j := by
      apply hi
      simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hij
    exact e.symm.injective h
  · intro hz
    obtain ⟨e, he⟩ := matrixEigenvalues_sorted_permutation n z hz
    exact Set.mem_iUnion.mpr ⟨e, (matrixSchurOrderedConfigurations_iff (z ∘ e)).mpr he⟩

#print axioms matrixSchurPermutationChamber_pairwise_disjoint
#print axioms matrixSchurPermutationChamber_cover
end
end GinibrePoincare
