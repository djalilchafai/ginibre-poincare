module

public import GinibrePoincare.Analysis.GinibreStochasticCenterRadialDriverIndependence
public import GinibrePoincare.Analysis.GinibreStochasticCenterSquaredDrivenLocal
public import GinibrePoincare.Analysis.GinibreStochasticCIRDrivenLocal

@[expose] public section

/-! Joint genuine center and relative CIR realizations. Positive speed and
positive initial center are explicit domain restrictions of this endpoint. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2000000

theorem ginibreBrownian_two_radius_independent_CIR_realization
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (hα : 0 < α)
    (z : Configuration n) (hz : CollisionFree z) (hcenter : 0 < ginibreCenterSquared n z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    ∃ βS βR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
        let aS := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*ginibreCenterSquared n (X t ω))
        let aR := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
        ∃ JS JR : ℝ≥0 → Ω → ℝ,
          Martingale JS F P ∧ Martingale JR F P ∧
          (∀ ω, Continuous (fun t => JS t ω)) ∧ (∀ ω, Continuous (fun t => JR t ω)) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum βS aS t (k+1) ω-JS t ω)^2 ∂P) atTop (𝓝 0)) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum βR aR t (k+1) ω-JR t ω)^2 ∂P) atTop (𝓝 0)) ∧
          ∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
            (ginibreCenterSquared n (X t ω)-ginibreCenterSquared n z = JS t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*(1-ginibreCenterSquared n (X s.toNNReal ω))) ∧
            (pairwiseRadius (X t ω)-pairwiseRadius z = JR t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
                ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  obtain ⟨βS, hβS, hβSM, hβSL, hβS0, hβSLim, hβSShift, hβSFresh⟩ :=
    ginibreBrownianMaximalProcess_center_Brownian_exists hn α z hz hcenter B P hB hind
  obtain ⟨βR, hβR, hβRM, hβRL, hβR0, hβRLim, hβRShift, hβRFresh⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  refine ⟨βS, βR, hβS, hβR,?_,?_⟩
  · exact ginibreBrownian_center_radial_Brownian_drivers_independent hn α hα z hz hcenter
      B P hB hind e e βS βR hβS.cont hβSLim hβR.cont hβRLim
  · intro R hR T
    obtain ⟨JS, hJSM, hJSC, hJSL, hJS0, hJSMS, hJSLim, hSIto⟩ :=
      ginibreBrownianMaximalProcess_local_center_CIR_Brownian_integral hn α z hz hcenter
        B P hB hind e he βS hβSL hβSLim R hR T
    obtain ⟨JR, hJRM, hJRC, hJRL, hJR0, hJRMS, hJRLim, hRIto⟩ :=
      ginibreBrownianMaximalProcess_local_CIR_Brownian_integral hn α z hz B P hB hind
        e he βR hβRL hβRLim R hR T
    refine ⟨JS, JR, hJSM, hJRM, hJSC, hJRC, hJSMS, hJRMS,?_⟩
    filter_upwards [hSIto, hRIto] with ω hs hr
    exact fun t ht => ⟨hs t ht, hr t ht⟩

#print axioms ginibreBrownian_two_radius_independent_CIR_realization
end
end GinibrePoincare
