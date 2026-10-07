module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLocalization

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalWeak_compact_L2_locallyIntegrable
    {n : ℕ} {V : Type*} [NormedAddCommGroup V]
    (g : Configuration n → V)
    (hg : ∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
      MemLp g 2 (volume.restrict K)) :
    LocallyIntegrableOn g {z : Configuration n | CollisionFree z} volume := by
  apply (locallyIntegrableOn_iff (isOpen_collisionFree n).isLocallyClosed).mpr
  intro K hs hc
  letI : IsFiniteMeasure (volume.restrict K : Measure (Configuration n)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hc.measure_lt_top⟩
  exact (hg K hc hs).integrable (by norm_num)

theorem ginibreLocalWeak_compact_L2_coordinates_locallyIntegrable
    {n : ℕ} (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hg : ∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
      MemLp g 2 (volume.restrict K)) :
    ∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume := by
  intro k
  let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
  exact P.locallyIntegrableOn_comp (ginibreLocalWeak_compact_L2_locallyIntegrable g hg)

#print axioms ginibreLocalWeak_compact_L2_locallyIntegrable
#print axioms ginibreLocalWeak_compact_L2_coordinates_locallyIntegrable
end
end GinibrePoincare
