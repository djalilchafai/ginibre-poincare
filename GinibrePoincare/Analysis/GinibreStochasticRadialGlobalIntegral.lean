module

public import GinibrePoincare.Analysis.GinibreStochasticRadialDirection
public import GinibrePoincare.Analysis.GinibreStochasticUnitFieldGlobalIntegral

@[expose] public section

/-! The radial noise is constructed from the original independent Brownian
family and the actual globally noncolliding canonical solution. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreBrownianMaximalProcess_radial_global_integral_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∃ (u : ℝ≥0 → Ω → EuclideanSpace ℝ (Fin n × Fin 2)) (J : ℝ≥0 → Ω → ℝ),
      (∀ t ω, u t ω = ginibreRecenteredRadialDirection n
        (EuclideanSpace.single (⟨0, by omega⟩, 0) 1)
        (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ᵐ ω ∂P, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun k ω => ∑ i,
        brownianUniformLeftSum (B i) (fun s ω => u s ω i) t (k+1) ω) atTop (J t)) ∧
      (∀ t, HasLaw (J t) (gaussianReal 0 t) P) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0, by omega⟩, 0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e, PiLp.norm_single]
  let u := fun t ω => ginibreRecenteredRadialDirection n e
    (ginibreBrownianMaximalProcess n α z B t ω)
  obtain ⟨hu, hunit, hc⟩ := ginibreBrownianMaximalProcess_radialDirection_properties
    hn α z hz B P hB hind e he
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS, hJlaw⟩ := ginibreUnitField_global_continuous_integral_exists
    B P hB hind u hu hunit hc i₀
  exact ⟨u, J, fun t ω => rfl, hJM, hJC, hJL, hJ0, hJS, hJlaw⟩
end
end GinibrePoincare
