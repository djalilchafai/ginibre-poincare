module
public import GinibrePoincare.Analysis.HermiteL2Family
public import Mathlib.Data.Prod.Lex
public import Mathlib.Order.Interval.Finset.Defs

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite

/-- Tensor orbital labels ordered first by total degree and then by their
injective natural-number encoding. -/
@[ext] structure DegreeHermiteIndex (n : ℕ) where
  val : HermiteMultiIndex n
deriving DecidableEq

def hermiteTotalDegree {n : ℕ} (i : HermiteMultiIndex n) : ℕ :=
  (∑ j, i.1 j) + ∑ j, i.2 j

def degreeHermiteKey {n : ℕ} (i : DegreeHermiteIndex n) : ℕ ×ₗ ℕ :=
  toLex (hermiteTotalDegree i.val, Encodable.encode i.val)

theorem degreeHermiteKey_injective (n : ℕ) :
    Function.Injective (@degreeHermiteKey n) := by
  intro i j h
  apply DegreeHermiteIndex.ext
  apply Encodable.encode_injective
  exact congrArg (fun k : ℕ ×ₗ ℕ => (ofLex k).2) h

instance (n : ℕ) : LinearOrder (DegreeHermiteIndex n) :=
  LinearOrder.lift' degreeHermiteKey (degreeHermiteKey_injective n)

instance (n : ℕ) : WellFoundedLT (DegreeHermiteIndex n) :=
  InvImage.wf degreeHermiteKey (wellFounded_lt (α := ℕ ×ₗ ℕ))

theorem finite_hermite_degree_sublevel (n D : ℕ) :
    {i : DegreeHermiteIndex n | hermiteTotalDegree i.val ≤ D}.Finite := by
  let f : ((Fin n → Fin (D+1)) × (Fin n → Fin (D+1))) → DegreeHermiteIndex n :=
    fun i => ⟨(fun j => (i.1 j).val, fun j => (i.2 j).val)⟩
  apply (Set.finite_range f).subset
  intro i hi
  have hp (j : Fin n) : i.val.1 j ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Nat.le_add_right _ _).trans hi)
  have hq (j : Fin n) : i.val.2 j ≤ D :=
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)).trans
      ((Nat.le_add_left _ _).trans hi)
  exact ⟨(fun j => ⟨i.val.1 j, Nat.lt_succ_of_le (hp j)⟩,
    fun j => ⟨i.val.2 j, Nat.lt_succ_of_le (hq j)⟩),rfl⟩

theorem degreeHermite_finite_Iic (n : ℕ) (i : DegreeHermiteIndex n) :
    (Set.Iic i).Finite := by
  apply (finite_hermite_degree_sublevel n (hermiteTotalDegree i.val)).subset
  intro j hj
  change degreeHermiteKey j ≤ degreeHermiteKey i at hj
  rcases Prod.Lex.le_iff.mp hj with h | ⟨h,_⟩
  · exact Nat.le_of_lt h
  · exact h.le

instance (n : ℕ) : LocallyFiniteOrderBot (DegreeHermiteIndex n) :=
  LocallyFiniteOrderBot.ofIic _ (fun i => (degreeHermite_finite_Iic n i).toFinset)
    (fun i j => by simp)

/-- Any strict drop in total degree precedes the original orbital label. -/
theorem degreeHermite_lt_of_degree_lt {n : ℕ} {i j : DegreeHermiteIndex n}
    (h : hermiteTotalDegree i.val < hermiteTotalDegree j.val) : i < j :=
  Prod.Lex.lt_iff.mpr (Or.inl h)

#print axioms degreeHermiteKey_injective
#print axioms finite_hermite_degree_sublevel
#print axioms degreeHermite_finite_Iic
#print axioms degreeHermite_lt_of_degree_lt
end
end GinibrePoincare
