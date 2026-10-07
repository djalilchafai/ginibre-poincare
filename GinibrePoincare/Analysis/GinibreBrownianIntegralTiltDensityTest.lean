module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltTestLimit

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology BoundedContinuousFunction
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Genuine L¹ changes of density and actual probability convergence of states
 preserve every bounded continuous weighted expectation. -/
theorem actualVaryingDensity_continuous_test_tendsto {Ω E : Type*} [MeasurableSpace Ω]
    [MetricSpace E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (P : Measure Ω) [IsFiniteMeasure P]
    (D : ℕ → Ω → ℝ) (d : Ω → ℝ) (hDi : ∀ n, Integrable (D n) P) (hdi : Integrable d P)
    (hL : Tendsto (fun n => eLpNorm (D n-d) 1 P) atTop (𝓝 0))
    (X : ℕ → Ω → E) (x : Ω → E) (hX : ∀ n, AEMeasurable (X n) P)
    (hx : AEMeasurable x P) (hl : TendstoInMeasure P X atTop x) (b : E →ᵇ ℝ) :
    Tendsto (fun n => ∫ ω, D n ω*b (X n ω) ∂P) atTop (𝓝 (∫ ω, d ω*b (x ω) ∂P)) := by
  have hbm (n : ℕ) : AEStronglyMeasurable (fun ω => b (X n ω)) P :=
    (b.continuous.measurable.comp_aemeasurable (hX n)).aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ ω ∂P, ‖b (X n ω)‖≤‖b‖ := Eventually.of_forall fun ω => b.norm_coe_le_norm _
  have hfixed := actualDensity_continuous_test_tendsto P d hdi X x hX hx hl b
  have herr := actualDensity_bounded_test_error_tendsto P D d hDi hdi hL
    (fun n ω => b (X n ω)) ‖b‖ (norm_nonneg _) (fun n ω => b.norm_coe_le_norm _)
  have he (n : ℕ) : (∫ ω, (D n ω-d ω)*b (X n ω) ∂P)+(∫ ω, d ω*b (X n ω) ∂P) =
      ∫ ω, D n ω*b (X n ω) ∂P := by
    change (∫ ω, (D n-d) ω*b (X n ω) ∂P)+(∫ ω, d ω*b (X n ω) ∂P)=_
    rw [← integral_add (((hDi n).sub hdi).mul_bdd (hbm n) (hb n))
      (hdi.mul_bdd (hbm n) (hb n))]
    congr 1
    funext ω
    simp only [Pi.sub_apply]
    ring
  simpa only [he,zero_add] using herr.add hfixed

end
end GinibrePoincare
