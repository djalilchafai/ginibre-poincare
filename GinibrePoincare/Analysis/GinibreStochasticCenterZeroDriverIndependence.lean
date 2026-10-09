module

public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiIncrementContinuous
public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroDriverRecovery
public import GinibrePoincare.Analysis.GinibreStochasticCenterRadialDriverIndependence

@[expose] public section

/-! The actual unrestricted center radial driver is a measurable functional of
the center path and is independent of the actual relative radial driver. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2400000

theorem ginibreBrownian_unrestricted_center_driver_eq_recovery
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω)) (hβ0 : β 0 =ᵐ[P] (fun _ => 0))
    (hβShift : ∀ a r, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B
      (fun u ω => ginibreCenterRadialDirection n e (ginibreBrownianMaximalProcess n α z B u ω))
      a r (k+1)) atTop (fun ω => β (a+r) ω-β a ω)) :
    (fun ω t => β t ω) =ᵐ[P] (fun ω => ginibreCenterPuncturedLampertiRecovery n α
      (fun t => coordinateSum (ginibreBrownianMaximalProcess n α z B t ω))) := by
  have hinc (k : ℕ) := ginibreBrownian_center_Lamperti_positive_start_all hn α hα z hz B P hB hind e β hβC hβShift
    (ginibreCenterPositiveStart k) (by dsimp [ginibreCenterPositiveStart]; positivity)
  have hX := (ginibreBrownianMaximalProcess_global_original_solution (by omega) α z hz B P hB hind).2
  have hnz := ginibreBrownian_center_all_positive_times_nonzero hn α hα z hz B P hB hind
  have hc : 0 < Real.sqrt (2*(α : ℝ)/(n : ℝ)) := Real.sqrt_pos.mpr
    (div_pos (mul_pos (by norm_num) (show 0 < (α : ℝ) from hα)) (by exact_mod_cast (show 0 < n by omega)))
  apply ginibreCenterPuncturedDriver_eq_recovery P n α _ β hβC hβ0
  filter_upwards [ae_all_iff.mpr hinc, hX, hnz] with ω hinc hx hnz
  intro k t ht
  have hS : Continuous (fun u : ℝ≥0 => coordinateSum (ginibreBrownianMaximalProcess n α z B u ω)) := by
    have hC : Continuous (fun u : ℝ≥0 => ginibreBrownianMaximalProcess n α z B u ω) := by
      simpa only [Function.comp_def, Real.toNNReal_coe] using hx.1.comp NNReal.continuous_coe
    simpa only [Function.comp_def, coordinateSumCLM_apply] using (coordinateSumCLM n).continuous.comp hC
  have hp (s : ℝ≥0) (hs : 0 < s) : 0 < Complex.normSq (coordinateSum (ginibreBrownianMaximalProcess n α z B s ω)) :=
    lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnz s hs))
  rw [ginibreCenterPositiveStartLamperti_eq_integral n α k _ hS hp t]
  have hh := hinc k (t-ginibreCenterPositiveStart k)
  rw [add_tsub_cancel_of_le ht] at hh
  apply (div_eq_iff hc.ne').mpr
  change Real.sqrt (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω))-
    Real.sqrt (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (ginibreCenterPositiveStart k) ω))-
    _ = _
  change Real.sqrt (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B t ω))-
    Real.sqrt (ginibreCenterSquared n (ginibreBrownianMaximalProcess n α z B (ginibreCenterPositiveStart k) ω)) = _ at hh
  unfold ginibreCenterSquared at hh ⊢
  nlinarith [hh]

theorem ginibreBrownian_unrestricted_center_radial_drivers_independent
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (eS eR : EuclideanSpace ℝ (Fin n × Fin 2)) (βS βR : ℝ≥0 → Ω → ℝ)
    (hβSC : ∀ᵐ ω ∂P, Continuous (fun t => βS t ω)) (hβS0 : βS 0 =ᵐ[P] (fun _ => 0))
    (hβSShift : ∀ a r, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B
      (fun u ω => ginibreCenterRadialDirection n eS (ginibreBrownianMaximalProcess n α z B u ω))
      a r (k+1)) atTop (fun ω => βS (a+r) ω-βS a ω))
    (hβRC : ∀ᵐ ω ∂P, Continuous (fun t => βR t ω))
    (hβRLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n eR (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k+1) ω) atTop (βR t)) :
    IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P := by
  have hi := (ginibreBrownian_center_radial_driver_independent hn α hα z hz B P hB hind
    eR βR hβRC hβRLim).comp (ginibreCenterPuncturedLampertiRecovery_measurable n α) measurable_id
  exact hi.congr
    (ginibreBrownian_unrestricted_center_driver_eq_recovery hn α hα z hz B P hB hind
      eS βS hβSC hβS0 hβSShift).symm Filter.EventuallyEq.rfl

#print axioms ginibreBrownian_unrestricted_center_driver_eq_recovery
#print axioms ginibreBrownian_unrestricted_center_radial_drivers_independent
end
end GinibrePoincare
