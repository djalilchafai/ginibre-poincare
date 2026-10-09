module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInteriorCutoff
public import Mathlib.Topology.Compactness.SigmaCompact

@[expose] public section

open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000

local instance ginibreLocalRegularityCF_locallyCompact (n : ℕ) :
    LocallyCompactSpace {z : Configuration n // CollisionFree z} :=
  (isOpen_collisionFree n).locallyCompactSpace

def ginibreLocalRegularityCFCompactExhaustion (n : ℕ) :
    CompactExhaustion {z : Configuration n // CollisionFree z} := CompactExhaustion.choice _

def ginibreLocalRegularityCompactSet (n j : ℕ) : Set (Configuration n) :=
  Subtype.val '' (ginibreLocalRegularityCFCompactExhaustion n j)

def ginibreLocalRegularityOpenSet (n j : ℕ) : Set (Configuration n) :=
  interior (ginibreLocalRegularityCompactSet n j)

theorem ginibreLocalRegularityCompactSet_isCompact (n j : ℕ) :
    IsCompact (ginibreLocalRegularityCompactSet n j) :=
  (ginibreLocalRegularityCFCompactExhaustion n).isCompact j |>.image continuous_subtype_val

theorem ginibreLocalRegularityCompactSet_subset (n j : ℕ) :
    ginibreLocalRegularityCompactSet n j ⊆ {z | CollisionFree z} := by
  rintro z ⟨x, hx, rfl⟩
  exact x.property

theorem ginibreLocalRegularityCompactSet_monotone (n : ℕ) :
    Monotone (ginibreLocalRegularityCompactSet n) := by
  intro i j hij
  exact image_mono ((ginibreLocalRegularityCFCompactExhaustion n).subset hij)

theorem ginibreLocalRegularityCompactSet_subset_open_succ (n j : ℕ) :
    ginibreLocalRegularityCompactSet n j ⊆ ginibreLocalRegularityOpenSet n (j+1) := by
  rintro z ⟨x, hx, rfl⟩
  exact (isOpen_collisionFree n).isOpenMap_subtype_val.image_interior_subset _
    ⟨x, (ginibreLocalRegularityCFCompactExhaustion n).subset_interior_succ j hx, rfl⟩

theorem ginibreLocalRegularityOpenSet_isOpen (n j : ℕ) :
    IsOpen (ginibreLocalRegularityOpenSet n j) := isOpen_interior

theorem ginibreLocalRegularityOpenSet_subset_compact (n j : ℕ) :
    ginibreLocalRegularityOpenSet n j ⊆ ginibreLocalRegularityCompactSet n j := interior_subset

theorem ginibreLocalRegularityOpenSet_monotone (n : ℕ) :
    Monotone (ginibreLocalRegularityOpenSet n) := by
  intro i j hij
  exact interior_mono (ginibreLocalRegularityCompactSet_monotone n hij)

theorem ginibreLocalRegularityOpenSet_iUnion (n : ℕ) :
    (⋃ j, ginibreLocalRegularityOpenSet n j) = {z | CollisionFree z} := by
  apply Subset.antisymm
  · exact iUnion_subset (fun j => (ginibreLocalRegularityOpenSet_subset_compact n j).trans
      (ginibreLocalRegularityCompactSet_subset n j))
  · intro z hz
    obtain ⟨j, hj⟩ := (ginibreLocalRegularityCFCompactExhaustion n).exists_mem ⟨z, hz⟩
    exact mem_iUnion.mpr ⟨j+1, ginibreLocalRegularityCompactSet_subset_open_succ n j ⟨⟨z, hz⟩, hj, rfl⟩⟩

theorem ginibreLocalRegularityOpenSet_contains_compact {n : ℕ}
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z}) :
    ∃ j, K ⊆ ginibreLocalRegularityOpenSet n j := by
  apply hK.elim_directed_cover (ginibreLocalRegularityOpenSet n)
    (ginibreLocalRegularityOpenSet_isOpen n)
  · intro z hz
    rw [ginibreLocalRegularityOpenSet_iUnion]
    exact hs hz
  · exact (ginibreLocalRegularityOpenSet_monotone n).directed_le

def ginibreLocalRegularityExhaustionCutoff (n : ℕ) (hn : 0 < n) (j : ℕ) : Configuration n → ℝ :=
  Classical.choose (ginibreLocalRegularity_exists_compact_interior_cutoff n hn
    (ginibreLocalRegularityCompactSet n j) (ginibreLocalRegularityCompactSet_isCompact n j)
    (ginibreLocalRegularityCompactSet_subset n j))

theorem ginibreLocalRegularityExhaustionCutoff_properties (n : ℕ) (hn : 0 < n) (j : ℕ) :
    ContDiff ℝ ∞ (ginibreLocalRegularityExhaustionCutoff n hn j) ∧
    HasCompactSupport (ginibreLocalRegularityExhaustionCutoff n hn j) ∧
    tsupport (ginibreLocalRegularityExhaustionCutoff n hn j) ⊆ {z | CollisionFree z} ∧
    ∀ z ∈ ginibreLocalRegularityCompactSet n j,
      ginibreLocalRegularityExhaustionCutoff n hn j =ᶠ[𝓝 z] 1 :=
  Classical.choose_spec (ginibreLocalRegularity_exists_compact_interior_cutoff n hn
    (ginibreLocalRegularityCompactSet n j) (ginibreLocalRegularityCompactSet_isCompact n j)
    (ginibreLocalRegularityCompactSet_subset n j))

theorem ginibreLocalRegularityExhaustionCutoff_one (n : ℕ) (hn : 0 < n) (j : ℕ)
    (z : Configuration n) (hz : z ∈ ginibreLocalRegularityCompactSet n j) :
    ginibreLocalRegularityExhaustionCutoff n hn j z = 1 :=
  ((ginibreLocalRegularityExhaustionCutoff_properties n hn j).2.2.2 z hz).eq_of_nhds

theorem ginibreLocalRegularityExhaustionCutoff_fderiv_zero (n : ℕ) (hn : 0 < n) (j : ℕ)
    (z : Configuration n) (hz : z ∈ ginibreLocalRegularityCompactSet n j) :
    fderiv ℝ (ginibreLocalRegularityExhaustionCutoff n hn j) z = 0 := by
  have he := ((ginibreLocalRegularityExhaustionCutoff_properties n hn j).2.2.2 z hz).fderiv_eq
    (𝕜 := ℝ)
  simpa using he

#print axioms ginibreLocalRegularityOpenSet_iUnion
#print axioms ginibreLocalRegularityOpenSet_contains_compact
#print axioms ginibreLocalRegularityExhaustionCutoff_properties
end
end GinibrePoincare
