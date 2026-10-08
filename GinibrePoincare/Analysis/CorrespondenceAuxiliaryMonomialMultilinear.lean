module

public import GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A coordinate word gives an actual continuous homogeneous multilinear map
whose diagonal is the corresponding holomorphic coordinate monomial. -/
def coordinateWordMultilinear {n k : ℕ} (word : Fin k → Fin n) :
    ContinuousMultilinearMap ℂ (fun _ : Fin k => Configuration n) ℂ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℂ k ℂ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (word i))

@[simp] theorem coordinateWordMultilinear_apply {n k : ℕ} (word : Fin k → Fin n)
    (v : Fin k → Configuration n) :
    coordinateWordMultilinear word v = ∏ i, v i (word i) := by
  simp [coordinateWordMultilinear,ContinuousMultilinearMap.mkPiAlgebraFin_apply,
    List.prod_ofFn]

/-- Uniform operator bound needed to construct the genuine multivariate
holomorphic Taylor series; this holds also in degree zero. -/
theorem coordinateWordMultilinear_norm_le {n k : ℕ} (word : Fin k → Fin n) :
    ‖coordinateWordMultilinear word‖ ≤ 1 := by
  apply ContinuousMultilinearMap.opNorm_le_bound (by norm_num)
  intro v
  rw [coordinateWordMultilinear_apply,norm_prod,one_mul]
  gcongr with i
  exact norm_le_pi_norm (v i) (word i)

/-- The canonical finite coordinate word with precisely the specified
multiplicities. -/
def monomialCoordinateWord {n : ℕ} (p : Fin n → ℕ) :
    Fin (∑ i, p i) → Fin n :=
  fun j => ((Fintype.equivFinOfCardEq
    (show Fintype.card (Σ i : Fin n, Fin (p i)) = ∑ i, p i by simp)).symm j).1

def holomorphicMonomialMultilinear {n : ℕ} (p : Fin n → ℕ) :
    ContinuousMultilinearMap ℂ (fun _ : Fin (∑ i, p i) => Configuration n) ℂ :=
  coordinateWordMultilinear (monomialCoordinateWord p)

@[simp] theorem holomorphicMonomialMultilinear_diagonal {n : ℕ}
    (p : Fin n → ℕ) (z : Configuration n) :
    holomorphicMonomialMultilinear p (fun _ => z) = ∏ i, z i ^ p i := by
  rw [holomorphicMonomialMultilinear,coordinateWordMultilinear_apply]
  let e := Fintype.equivFinOfCardEq
    (show Fintype.card (Σ i : Fin n, Fin (p i)) = ∑ i, p i by simp)
  change (∏ j : Fin (∑ i, p i), z (e.symm j).1) = _
  rw [e.symm.prod_comp (fun j : Σ i : Fin n, Fin (p i) => z j.1)]
  simp [Fintype.prod_sigma]

theorem holomorphicMonomialMultilinear_norm_le {n : ℕ} (p : Fin n → ℕ) :
    ‖holomorphicMonomialMultilinear p‖ ≤ 1 :=
  coordinateWordMultilinear_norm_le _

/-- Every homogeneous multivariate degree contains only finitely many
monomials, including the zero-dimensional case. -/
theorem finite_holomorphic_degree_fiber (n k : ℕ) :
    Set.Finite {p : Fin n → ℕ | ∑ i, p i = k} := by
  let f : {p : Fin n → ℕ // ∑ i, p i = k} → (Fin n → Fin (k+1)) :=
    fun p i => ⟨p.val i, by
      have hi : p.val i ≤ ∑ j, p.val j := Finset.single_le_sum
        (fun j _ => Nat.zero_le (p.val j)) (Finset.mem_univ i)
      omega⟩
  have hf : Function.Injective f := by
    intro p q h
    apply Subtype.ext
    funext i
    exact congrArg Fin.val (congrFun h i)
  exact Set.finite_coe_iff.mp (Finite.of_injective f hf)

#print axioms finite_holomorphic_degree_fiber
#print axioms holomorphicMonomialMultilinear_diagonal
#print axioms holomorphicMonomialMultilinear_norm_le
#print axioms coordinateWordMultilinear_apply
#print axioms coordinateWordMultilinear_norm_le
end
end GinibrePoincare
