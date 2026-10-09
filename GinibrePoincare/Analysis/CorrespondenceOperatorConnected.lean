module
public import GinibrePoincare.Concrete.Configuration
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section
/-- Collision-free configurations can be joined without collisions. The complex
line between two configurations has only finitely many forbidden parameters. -/
theorem correspondenceOperator_collisionFree_joined {n : ℕ}
    (z w : Configuration n) (hz : CollisionFree z) (hw : CollisionFree w) :
    JoinedIn {x : Configuration n | CollisionFree x} z w := by
  classical
  let bad : Set ℂ := Set.range (fun p : Fin n × Fin n =>
    -(z p.1-z p.2)/((w p.1-z p.1)-(w p.2-z p.2)))
  let forbidden : Set ℂ := bad \ {0, 1}
  have hf : forbidden.Countable := (Set.finite_range _).countable.mono Set.sdiff_subset
  have hrank : 1 < Module.rank ℝ ℂ := by
    rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]
    norm_num
  have hpath := hf.isPathConnected_compl_of_one_lt_rank hrank
  have h0 : (0 : ℂ) ∈ forbiddenᶜ := by simp [forbidden]
  have h1 : (1 : ℂ) ∈ forbiddenᶜ := by simp [forbidden]
  let F : ℂ → Configuration n := fun a => z+a • (w-z)
  have hc : Continuous F := continuous_const.add (continuous_id.smul continuous_const)
  have himage : F '' forbiddenᶜ ⊆ {x : Configuration n | CollisionFree x} := by
    rintro x ⟨a, ha, rfl⟩
    by_cases ha0 : a=0
    · simpa [F, ha0] using hz
    by_cases ha1 : a=1
    · simpa [F, ha1] using hw
    intro i j hij
    by_contra hne
    have hzij : z i-z j≠0 := sub_ne_zero.mpr (fun h => hne (hz h))
    have heq : (z i-z j)+a*((w i-z i)-(w j-z j))=0 := by
      change z i+a*(w i-z i)=z j+a*(w j-z j) at hij
      linear_combination hij
    have hd : (w i-z i)-(w j-z j)≠0 := by
      intro hd
      rw [hd, mul_zero, add_zero] at heq
      exact hzij heq
    have hab : a∈bad := by
      refine ⟨(i, j),?_⟩
      apply (div_eq_iff hd).mpr
      linear_combination -heq
    exact ha ⟨hab, by simp [ha0, ha1]⟩
  have hh := (hpath.joinedIn 0 h0 1 h1).map hc.continuousOn
  have hh' := hh.mono himage
  simpa [F] using hh'
/-- The concrete collision-free configuration domain is path connected. -/
theorem correspondenceOperator_collisionFree_isPathConnected (n : ℕ) :
    IsPathConnected {x : Configuration n | CollisionFree x} := by
  apply isPathConnected_iff.mpr
  refine ⟨?_, fun z hz w hw => correspondenceOperator_collisionFree_joined z w hz hw⟩
  refine ⟨fun i => (i.val : ℂ),?_⟩
  intro i j hij
  exact Fin.ext (Nat.cast_injective hij)
#print axioms correspondenceOperator_collisionFree_isPathConnected
#print axioms correspondenceOperator_collisionFree_joined
end
end GinibrePoincare
