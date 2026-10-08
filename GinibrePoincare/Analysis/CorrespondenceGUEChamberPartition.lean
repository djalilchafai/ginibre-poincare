module
public import GinibrePoincare.Analysis.CorrespondenceGUEH1Closure
public import Mathlib.Data.Fin.Tuple.Sort
@[expose] public section
open MeasureTheory Set Function
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def guePermute (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun i => x (σ i))

theorem gueChamber_permutation_unique (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (σ τ : Equiv.Perm (Fin n)) (hσ : guePermute n σ x∈gueStrictChamber n)
    (hτ : guePermute n τ x∈gueStrictChamber n) : σ=τ := by
  have hI : Injective (fun i => x i) := by
    have h := (show StrictMono (fun i => x (σ i)) from hσ).injective
    intro i j hij
    have he := h (a₁ := σ.symm i) (a₂ := σ.symm j) (by simpa using hij)
    exact σ.symm.injective he
  have he := Tuple.unique_monotone
    (show StrictMono (fun i => x (σ i)) from hσ).monotone
    (show StrictMono (fun i => x (τ i)) from hτ).monotone
  apply Equiv.ext
  intro i
  exact hI (congrFun he i)

theorem gueChamber_sorted (n : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (hx : Injective (fun i => x i)) :
    guePermute n (Tuple.sort (fun i => x i)) x∈gueStrictChamber n := by
  intro i j hij
  have hm := Tuple.monotone_sort (fun i => x i) hij.le
  exact lt_of_le_of_ne hm (fun he => hij.ne ((Tuple.sort _).injective (hx he)))

theorem gueChamber_density_partition (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∑σ : Equiv.Perm (Fin n),gueOrderedRawDensity n (guePermute n σ x))=gueRawDensity n x := by
  by_cases hx : Injective (fun i => x i)
  · let σ := Tuple.sort (fun i => x i)
    rw [Finset.sum_eq_single σ]
    · rw [gueOrderedRawDensity_eq_chamber_density,ite_eq_left (gueChamber_sorted n x hx)]
      exact gueRawDensity_symmetric n σ x
    · intro τ hτ ht
      rw [gueOrderedRawDensity_eq_chamber_density]
      apply ite_eq_right
      intro hch
      exact ht (gueChamber_permutation_unique n x τ σ hch (gueChamber_sorted n x hx))
    · simp
  · have hz : gueRawDensity n x=0 := by
      rw [gueRawDensity_zero_iff_collision]
      simp only [Injective,not_forall] at hx
      obtain ⟨i,j,he,hn⟩ := hx
      exact ⟨i,j,hn,he⟩
    rw [hz]
    apply Finset.sum_eq_zero
    intro σ hσ
    rw [gueOrderedRawDensity_eq_chamber_density]
    by_cases hc : guePermute n σ x∈gueStrictChamber n
    · rw [ite_eq_left hc]
      exact (gueRawDensity_symmetric n σ x).trans hz
    · exact ite_eq_right hc

#print axioms gueChamber_density_partition
end
end GinibrePoincare
