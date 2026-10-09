module

public import GinibrePoincare.Analysis.GinibreEqualityWeakDeficit

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
set_option maxHeartbeats 600000

/-- Sharp equality pairs form a genuine linear subspace of the actual weak domain. -/
def ginibreFullWeakEqualitySpace (n : ℕ) (hn : 0 < n) : Submodule ℝ (ginibreFullWeakSpace n hn) where
  carrier := {p | ∀ q : ginibreFullWeakSpace n hn,
    (1 / (n : ℝ)) * inner ℝ p.val.2 q.val.2 =
      2 * inner ℝ (ginibreFullCenter n hn p.val.1) (ginibreFullCenter n hn q.val.1)}
  zero_mem' := by intro q; simp
  add_mem' := by
    intro p r hp hr q
    change (1 / (n : ℝ)) * inner ℝ (p.val.2+r.val.2) q.val.2 =
      2 * inner ℝ (ginibreFullCenter n hn (p.val.1+r.val.1)) (ginibreFullCenter n hn q.val.1)
    rw [map_add, inner_add_left, inner_add_left]
    linarith [hp q, hr q]
  smul_mem' := by
    intro c p hp q
    change (1 / (n : ℝ)) * inner ℝ (c • p.val.2) q.val.2 =
      2 * inner ℝ (ginibreFullCenter n hn (c • p.val.1)) (ginibreFullCenter n hn q.val.1)
    rw [map_smul, real_inner_smul_left, real_inner_smul_left]
    calc
      _ = c * ((1 / (n : ℝ)) * inner ℝ p.val.2 q.val.2) := by ring
      _ = c * (2 * inner ℝ (ginibreFullCenter n hn p.val.1) (ginibreFullCenter n hn q.val.1)) :=
        congrArg (c * ·) (hp q)
      _ = _ := by ring

theorem ginibreFullWeakEqualitySpace_mem_iff (n : ℕ) (hn : 0 < n)
    (p : ginibreFullWeakSpace n hn) :
    p ∈ ginibreFullWeakEqualitySpace n hn ↔
      ginibreWeakEnergy n p.val.2 = 2 * ginibreL2Variance n hn p.val.1 :=
  (ginibreEquality_weak_variational_iff n hn p).symm

/-- Equality extends across every actual real weak-domain affine line. -/
theorem ginibreEquality_weak_linear_combination {n : ℕ} (hn : 0 < n)
    (p q : ginibreFullWeakSpace n hn) (a b : ℝ)
    (hp : ginibreWeakEnergy n p.val.2 = 2 * ginibreL2Variance n hn p.val.1)
    (hq : ginibreWeakEnergy n q.val.2 = 2 * ginibreL2Variance n hn q.val.1) :
    ginibreWeakEnergy n (a•p+b•q).val.2 =
      2 * ginibreL2Variance n hn (a•p+b•q).val.1 := by
  apply (ginibreFullWeakEqualitySpace_mem_iff n hn _).mp
  exact (ginibreFullWeakEqualitySpace n hn).add_mem
    ((ginibreFullWeakEqualitySpace n hn).smul_mem a ((ginibreFullWeakEqualitySpace_mem_iff n hn p).mpr hp))
    ((ginibreFullWeakEqualitySpace n hn).smul_mem b ((ginibreFullWeakEqualitySpace_mem_iff n hn q).mpr hq))

end GinibrePoincare
