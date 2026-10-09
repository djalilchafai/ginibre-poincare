module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingGlobalEnergy
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingGreen

@[expose] public section

open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1400000

theorem ginibreLocalWeak_global_distributional_pair {n : ℕ} (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n)) (hg : MemLp g 2 (ginibreMeasure n))
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k*θ z)=-(∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k))) :
    IsGinibreDistributionalGradient n (hu.toLp u) (hg.toLp g) := by
  refine ⟨ginibre_memLp_locallyIntegrable_collisionFree hn _ (Lp.memLp _),?_,?_⟩
  · intro k
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact ginibre_memLp_locallyIntegrable_collisionFree hn _ (P.comp_memLp (hg.toLp g))
  · intro k θ hθ hc hs
    have hu' := (ginibre_ae_eq_iff_volume n hn _ _).mp hu.coeFn_toLp
    have hg' := (ginibre_ae_eq_iff_volume n hn _ _).mp hg.coeFn_toLp
    have hl : (∫ z, hg.toLp g z k*θ z) = (∫ z, g z k*θ z) := by
      apply integral_congr_ae
      filter_upwards [hg'] with z hz
      rw [hz]
    have hr : (∫ z, hu.toLp u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        (∫ z, u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
      apply integral_congr_ae
      filter_upwards [hu'] with z hz
      rw [hz]
    rw [hl, hr]
    exact hw k θ hθ hc hs

#print axioms ginibreLocalWeak_global_distributional_pair
end
end GinibrePoincare
