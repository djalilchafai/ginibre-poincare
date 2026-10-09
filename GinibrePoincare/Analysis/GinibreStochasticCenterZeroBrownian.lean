module

public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroDirection
public import GinibrePoincare.Analysis.GinibreStochasticPuncturedUnitFieldBrownian

@[expose] public section

/-! An actual center radial Brownian driver is constructed from the original Ginibre
Brownian SDE. Its fresh increments are independent of the entire original past. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

theorem ginibreBrownianMaximalProcess_center_unrestricted_Brownian_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single (⟨0, by omega⟩, 0) 1
    let u := fun t ω => ginibreCenterRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B t ω)
    ∃ β : ℝ≥0 → Ω → ℝ,
      IsBrownianReal β P ∧
      Martingale β (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ t, MemLp (β t) 2 P) ∧ β 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω => ∑ i,
        brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (β t)) ∧
      (∀ s t, TendstoInMeasure P (fun k => brownianUnitShiftedUniformSum B u s t (k+1))
        atTop (fun ω => β (s+t) ω-β s ω)) ∧
      (∀ s t (Y : Ω → ℝ),
        @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) s) _ Y →
        IndepFun Y (fun ω => β (s+t) ω-β s ω) P) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  obtain ⟨hu, hunit, hc⟩ := ginibreBrownianMaximalProcess_centerDirection_punctured_properties
    hn α hα z hz B P hB hind e he
  exact ginibrePuncturedUnitField_Brownian_exists B P hB hind _ hu hunit hc i₀
#print axioms ginibreBrownianMaximalProcess_center_unrestricted_Brownian_exists
end
end GinibrePoincare
