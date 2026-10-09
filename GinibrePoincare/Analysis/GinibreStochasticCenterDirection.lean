module

public import GinibrePoincare.Analysis.GinibreStochasticCenterGlobalNonvanishing
public import GinibrePoincare.Analysis.GinibreStochasticRadialDirection

@[expose] public section

/-! The normalized center direction of the actual original Brownian solution.
Continuity follows from proved center non-hitting, for positive initial center. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

def ginibreRepeatedCenterCLM (n : ℕ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun _ => coordinateSumCLM n

def ginibreCenterRadialDirection (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  brownianRadialUnitVector (configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z)) e

theorem ginibreCenterRadialDirection_norm (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖=1) (z : Configuration n) :
    ‖ginibreCenterRadialDirection n e z‖=1 := brownianRadialUnitVector_norm _ e he

theorem ginibreCenterRadialDirection_measurable (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Measurable (ginibreCenterRadialDirection n e) :=
  (brownianRadialUnitVector_measurable e).comp
    ((configurationEuclideanEquiv n).continuous.measurable.comp (ginibreRepeatedCenterCLM n).measurable)

theorem ginibreCenterRadialDirection_continuousAt {n : ℕ} (hn : 0 < n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n)
    (hz : ginibreCenterSquared n z ≠ 0) : ContinuousAt (ginibreCenterRadialDirection n e) z := by
  have hne : configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n z) ≠ 0 := by
    intro h
    have he : ginibreRepeatedCenterCLM n z = 0 :=
      (configurationEuclideanEquiv n).injective (by simpa using h)
    have hi := congrFun he (⟨0, hn⟩ : Fin n)
    have hs : coordinateSum z=0 := by
      simpa only [ginibreRepeatedCenterCLM, ContinuousLinearMap.pi_apply,
        coordinateSumCLM_apply, Pi.zero_apply] using hi
    apply hz
    simp [ginibreCenterSquared, hs]
  have hc : ContinuousAt (fun x => configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n x)) z :=
    ((configurationEuclideanEquiv n).continuous.comp (ginibreRepeatedCenterCLM n).continuous).continuousAt
  exact (brownianRadialUnitVector_continuousAt _ e hne).comp
    (f := fun x => configurationEuclideanEquiv n (ginibreRepeatedCenterCLM n x)) hc

theorem ginibreBrownianMaximalProcess_centerDirection_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖=1) :
    let u := fun t ω => ginibreCenterRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B t ω)
    (∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin n × Fin 2))
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t)) ∧
    (∀ t ω, ‖u t ω‖=1) ∧ (∀ᵐ ω ∂P, Continuous (fun t => u t ω)) := by
  dsimp only
  obtain ⟨hAdapt, hPath⟩ := ginibreBrownianMaximalProcess_global_original_solution
    (by omega) α z hz B P hB hind
  refine ⟨fun t => (ginibreCenterRadialDirection_measurable n e).comp
    (hAdapt t).measurable, fun t ω => ginibreCenterRadialDirection_norm n e he _,?_⟩
  filter_upwards [hPath, ginibreBrownian_center_global_nonvanishing hn α z hz hcenter B P hB hind]
    with ω hω hnonzero
  have hX : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
    simpa only [Function.comp_def, Real.toNNReal_coe] using hω.1.comp NNReal.continuous_coe
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (ginibreCenterRadialDirection_continuousAt (by omega) e _ (hnonzero t)).comp
    (f := fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B s ω) hX.continuousAt

end
end GinibrePoincare
