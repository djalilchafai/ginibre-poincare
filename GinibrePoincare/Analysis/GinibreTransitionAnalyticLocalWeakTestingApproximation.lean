module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingLeibniz

@[expose] public section

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 100000


theorem ginibreLocalWeak_gradient_tsupport {n : ℕ} (η : Configuration n → ℝ) :
    tsupport (ginibreEuclideanGradient η) ⊆ tsupport η := by
  apply closure_minimal _ (isClosed_tsupport η)
  intro z hz
  by_contra hn
  have hd : fderiv ℝ η z = 0 := fderiv_of_notMem_tsupport ℝ hn
  apply hz
  ext k
  simp only [ginibreEuclideanGradient_coordinate, hd, ContinuousLinearMap.zero_apply, PiLp.zero_apply]

theorem ginibreLocalWeak_cutoff_smooth_sequence {n : ℕ} (hn : 0 < n)
    (u : Configuration n → ℝ) (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume)
    (hgl : ∀ k : Fin n × Fin 2, LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume)
    (hw : ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)))
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η)
    (hc : HasCompactSupport η) (hs : tsupport η ⊆ {z | CollisionFree z})
    (hv : MemLp (fun z => η z*u z) 2 (ginibreMeasure n))
    (hG : MemLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z) 2 (ginibreMeasure n)) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
        Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ ginibreInteriorSmoothPair n) ∧
      Tendsto q atTop (𝓝 (hv.toLp (fun z => η z*u z),
        hG.toLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z))) := by
  let v := hv.toLp (fun z => η z*u z)
  let G := hG.toLp (fun z => η z • g z + u z • ginibreEuclideanGradient η z)
  have hv' : (v : Configuration n → ℝ) =ᵐ[ginibreMeasure n] (fun z => η z*u z) := hv.coeFn_toLp
  have hG' : (G : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      (fun z => η z • g z + u z • ginibreEuclideanGradient η z) := hG.coeFn_toLp
  have hd := ginibreLocalWeak_distributional_gradient_mul n hn u g hu hgl hw η hη v G hv' hG'
  have hvC : HasCompactSupport (fun z => η z*u z) := hc.mul_right
  have hGC : HasCompactSupport (fun z => η z • g z + u z • ginibreEuclideanGradient η z) :=
    (hc.smul_right (f' := g)).add
      ((compactSupport_ginibreEuclideanGradient η hc).smul_left (f := u))
  have hvS : tsupport (fun z => η z*u z) ⊆ {z | CollisionFree z} :=
    tsupport_mul_subset_left.trans hs
  have hGS : tsupport (fun z => η z • g z + u z • ginibreEuclideanGradient η z) ⊆ {z | CollisionFree z} :=
    (tsupport_add (fun z => η z • g z) (fun z => u z • ginibreEuclideanGradient η z)).trans
      (Set.union_subset
        ((tsupport_smul_subset_left η g).trans hs)
        ((tsupport_smul_subset_right u (ginibreEuclideanGradient η)).trans
          ((ginibreLocalWeak_gradient_tsupport η).trans hs)))
  exact ginibreInteriorWeakPair_exists_smoothSequence hn v G hd _ _ hv' hG' hvC hGC hvS hGS

#print axioms ginibreLocalWeak_cutoff_smooth_sequence
end
end GinibrePoincare
