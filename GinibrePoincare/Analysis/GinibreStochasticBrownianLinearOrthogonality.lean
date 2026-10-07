module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadratic

@[expose] public section

/-! # Actual orthogonality of predictable centered quadratic innovations -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem ginibreBrownian_predictable_linear_cross_zero {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (si ti sj tj : ℝ≥0) (hij : si+ti ≤ sj)
    (Fi : (Set.Iic si → ℝ) → ℝ) (Fj : (Set.Iic sj → ℝ) → ℝ)
    (hFi : Measurable Fi) (hFj : Measurable Fj) :
    (∫ ω, (Fi (fun v => B v ω)*(B (si+ti) ω-B si ω))*
      (Fj (fun v => B v ω)*(B (sj+tj) ω-B sj ω)) ∂P) = 0 := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  have hsi : si ≤ sj := (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ ti from bot_le)).trans hij
  let Past := fun ω (v : Set.Iic sj) => B v ω
  let Z := fun ω => B (sj+tj) ω-B sj ω
  let G : (Set.Iic sj → ℝ) → ℝ := fun p =>
    Fi (fun v => p ⟨v, v.2.trans hsi⟩)*
      (p ⟨si+ti, hij⟩-p ⟨si, hsi⟩)*Fj p
  have hPast : Measurable Past := by
    apply measurable_pi_lambda
    intro v
    exact aemeasurable_iff_measurable.mp (hB.aemeasurable v)
  have hG : Measurable G := by
    dsimp [G]
    fun_prop
  have hZ : HasLaw Z (gaussianReal 0 tj) P := by
    simpa only [add_tsub_cancel_left] using ginibreBrownian_increment_hasLaw B P hB.toIsPreBrownianReal sj (sj+tj)
      (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ tj from bot_le))
  have hInd : IndepFun (fun ω => G (Past ω)) Z P :=
    (ginibreBrownian_increment_whole_past_independent B P hB.toIsPreBrownianReal sj tj).symm.comp hG measurable_id
  have hMean : (∫ ω, Z ω ∂P) = 0 := by
    have h := hZ.integral_comp (show AEStronglyMeasurable (fun x : ℝ => x) (gaussianReal 0 tj) by fun_prop)
    simpa only [Function.comp_apply, integral_id_gaussianReal] using h
  have hProd := hInd.integral_mul_eq_mul_integral
    (hG.comp hPast).aestronglyMeasurable hZ.aemeasurable.aestronglyMeasurable
  simp only [Pi.mul_apply, hMean, mul_zero] at hProd
  convert! hProd using 1
  congr 1
  funext ω
  dsimp [G, Past, Z]
  ring

end
end GinibrePoincare
