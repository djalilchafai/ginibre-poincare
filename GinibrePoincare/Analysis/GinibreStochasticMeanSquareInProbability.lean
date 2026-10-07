module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticVariation
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Mean-square convergence implies actual convergence in probability by Chebyshev. -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem ginibre_tendstoInMeasure_of_meanSquare {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (f : ℕ → Ω → ℝ) (g : Ω → ℝ)
    (hi : ∀ n, Integrable (fun ω => (f n ω-g ω)^2) P)
    (hlim : Tendsto (fun n => ∫ ω, (f n ω-g ω)^2 ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P f atTop g := by
  rw [tendstoInMeasure_iff_measureReal_norm]
  intro ε hε
  have hs (n : ℕ) : {ω | ε ≤ ‖f n ω-g ω‖} = {ω | ε^2 ≤ (f n ω-g ω)^2} := by
    ext ω
    simp only [Set.mem_setOf_eq, Real.norm_eq_abs]
    constructor
    · intro h
      nlinarith [sq_abs (f n ω-g ω)]
    · intro h
      nlinarith [sq_abs (f n ω-g ω), abs_nonneg (f n ω-g ω)]
  simp_rw [hs]
  apply squeeze_zero (fun n => measureReal_nonneg)
    (fun n => (le_div_iff₀ (sq_pos_of_pos hε)).mpr
      (by simpa only [mul_comm] using (mul_meas_ge_le_integral_of_nonneg
        (Filter.Eventually.of_forall fun ω => sq_nonneg (f n ω-g ω)) (hi n) (ε^2))))
  simpa only [zero_div] using hlim.div_const (ε^2)

theorem ginibreBrownianUniformQuadraticSum_tendstoInProbability {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    TendstoInMeasure P (fun n => ginibreBrownianUniformQuadraticSum B t n) atTop (fun _ => (t : ℝ)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  apply ginibre_tendstoInMeasure_of_meanSquare P _ _ _
    (ginibreBrownianUniformQuadraticSum_tendsto_meanSquare B P hB t)
  intro n
  have h := ginibreBrownianQuadraticSum_memLp_two B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  exact (h.sub (memLp_const (t : ℝ))).integrable_sq

end
end GinibrePoincare
