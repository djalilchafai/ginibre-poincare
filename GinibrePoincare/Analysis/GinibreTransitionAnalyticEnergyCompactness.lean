module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticCaccioppoli
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

@[expose] public section

/-! Genuine L² membership follows from locally cut off finite-energy bounds
and almost-everywhere convergence. -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000

theorem actualL2_toLp_norm_sq {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (f : Ω → E) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq]

theorem actualL2Limit_memLp_of_energy_bound {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (μ : Measure Ω)
    (f : ℕ → Ω → E) (g : Ω → E) (hf : ∀ n, MemLp (f n) 2 μ)
    (hg : AEStronglyMeasurable g μ) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ n, (∫ x, ‖f n x‖^2 ∂μ) ≤ D)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) : MemLp g 2 μ := by
  have hn (n : ℕ) : ‖(hf n).toLp (f n)‖ ≤ Real.sqrt D := by
    have hh := hb n
    rw [← actualL2_toLp_norm_sq μ (f n) (hf n)] at hh
    exact (Real.le_sqrt (norm_nonneg _) hD).mpr hh
  have he (n : ℕ) : eLpNorm (f n) 2 μ ≤ ENNReal.ofReal (Real.sqrt D) := by
    rw [← Lp.enorm_toLp (hf n),← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hn n)
  exact (Lp.eLpNorm_le_of_ae_tendsto (Eventually.of_forall he) (fun n => (hf n).aestronglyMeasurable) hg ht).trans_lt
    ENNReal.ofReal_lt_top

#print axioms actualL2_toLp_norm_sq
#print axioms actualL2Limit_memLp_of_energy_bound
end
end GinibrePoincare
