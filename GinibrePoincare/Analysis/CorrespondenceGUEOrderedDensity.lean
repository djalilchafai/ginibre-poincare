module
public import GinibrePoincare.Analysis.CorrespondenceGUEMarginalIntegrals
@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem gueOrderedRawDensity_eq_chamber_density (n : ℕ)
    (x : EuclideanSpace ℝ (Fin n)) :
    gueOrderedRawDensity n x=if x∈gueStrictChamber n then gueRawDensity n x else 0 := by
  by_cases hx : x∈gueStrictChamber n
  · rw [ite_eq_left hx]
    unfold gueOrderedRawDensity gueRawDensity
    congr 1
    · rw [EuclideanSpace.norm_sq_eq]
      simp only [Real.norm_eq_abs,sq_abs]
    · apply Finset.prod_congr rfl
      intro p hp
      have hij := (Finset.mem_filter.mp hp).2
      exact ite_eq_left (sub_pos.mpr (hx _ _ hij))
  · rw [ite_eq_right hx]
    unfold gueOrderedRawDensity
    have he : ∃p∈guePairs n, ¬(0<x p.2-x p.1) := by
      simp only [gueStrictChamber,mem_ofPred_eq,not_forall] at hx
      obtain ⟨i,j,hij,hgap⟩ := hx
      exact ⟨(i,j),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hij⟩,
        fun h => hgap (sub_pos.mp h)⟩
    obtain ⟨p,hp,hgap⟩ := he
    have hz : gueOrderedPairWeight (x p.2-x p.1)=0 := ite_eq_right hgap
    rw [Finset.prod_eq_zero hp hz,mul_zero]

#print axioms gueOrderedRawDensity_eq_chamber_density
end
end GinibrePoincare
