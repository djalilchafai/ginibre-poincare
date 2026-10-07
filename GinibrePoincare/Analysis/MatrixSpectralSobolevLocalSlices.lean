module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

/-! # Ordinary local integrability on almost every real coordinate line -/
open MeasureTheory Filter
namespace GinibrePoincare
noncomputable section

theorem locallyIntegrable_real_product_slices
    {Y : Type*} [NormedAddCommGroup Y] [ProperSpace Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (ν : Measure Y) [SFinite ν] (f : ℝ × Y → ℝ)
    (hf : LocallyIntegrable f ((volume : Measure ℝ).prod ν)) :
    ∀ᵐ y ∂ν, LocallyIntegrable (fun t => f (t, y)) volume := by
  have hi (k : ℕ) : Integrable
      ((Metric.closedBall (0 : ℝ × Y) (k : ℝ)).indicator f)
      ((volume : Measure ℝ).prod ν) :=
    (hf.integrableOn_isCompact (isCompact_closedBall _ _)).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have ha : ∀ᵐ y ∂ν, ∀ k : ℕ, Integrable
      (fun t => (Metric.closedBall (0 : ℝ × Y) (k : ℝ)).indicator f (t, y)) volume :=
    ae_all_iff.mpr fun k => (hi k).prod_left_ae
  filter_upwards [ha] with y hy
  intro t
  obtain ⟨k, hk⟩ := exists_nat_gt (‖(t, y)‖ + 1)
  refine ⟨Metric.ball t 1, Metric.ball_mem_nhds t zero_lt_one, ?_⟩
  apply ((hy k).integrableOn).congr_fun _ Metric.isOpen_ball.measurableSet
  intro s hs
  apply Set.indicator_of_mem
  rw [Metric.mem_closedBall, dist_zero_right]
  have hst : ‖s - t‖ < 1 := by simpa [Real.dist_eq] using hs
  have hd : ‖(s, y) - (t, y)‖ < 1 := by simpa [Prod.norm_def] using hst
  have hb := norm_le_norm_sub_add (s, y) (t, y)
  linarith

end
end GinibrePoincare
