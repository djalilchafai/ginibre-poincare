module

public import GinibrePoincare.Analysis.BrownianIntegralContinuousModificationExistence
public import GinibrePoincare.Analysis.GinibreBrownianIntegralLimitAdaptation

@[expose] public section

open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- The actual pathwise subsequence limit equals the genuine Hilbert-space
limit almost everywhere; no measurability of the pathwise candidate is assumed. -/
theorem actualL2Limit_eq_pathwise_subsequence_ae
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : ℕ → Ω → ℝ) (hs : ∀ n, MemLp (S n) 2 P)
    (I : Lp ℝ 2 P) (hI : Tendsto (fun n => (hs n).toLp (S n)) atTop (𝓝 I))
    (s : ℕ → ℕ) (hsmono : StrictMono s) (L : Ω → ℝ)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun n => S (s n) ω) atTop (𝓝 (L ω))) :
    L =ᵐ[P] (fun ω => I ω) := by
  have hsub := hI.comp hsmono.tendsto_atTop
  have hp : TendstoInMeasure P (fun n => S (s n)) atTop (fun ω => I ω) :=
    (tendstoInMeasure_of_tendsto_Lp hsub).congr
      (fun n => (hs (s n)).coeFn_toLp) EventuallyEq.rfl
  obtain ⟨r, hr, ha⟩ := hp.exists_seq_tendsto_ae
  filter_upwards [hL, ha] with ω hl hi
  exact tendsto_nhds_unique (hl.comp hr.tendsto_atTop) hi

/-- At every earlier time, terminal mean-square Cauchy estimates control the
actual marginal differences by conditional Jensen. -/
theorem realMartingale_difference_secondMoment_le_terminal
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (M N : ℝ≥0 → Ω → ℝ)
    (hM : Martingale M ℱ P) (hN : Martingale N ℱ P)
    (T t : ℝ≥0) (ht : t ≤ T) (hMT : MemLp (M T) 2 P) (hNT : MemLp (N T) 2 P) :
    (∫ ω, (M t ω-N t ω)^2 ∂P) ≤ ∫ ω, (M T ω-N T ω)^2 ∂P := by
  have hc := (hM.sub hN).condExp_ae_eq ht
  calc
    _ = ∫ ω, (P[(fun ω => M T ω-N T ω) | ℱ t] ω)^2 ∂P := by
      apply integral_congr_ae
      filter_upwards [hc] with ω hω
      exact congrArg (fun r : ℝ => r^2) hω.symm
    _ ≤ _ := real_condExp_square_integral_le P (ℱ t) (ℱ.le t) _ (hMT.sub hNT)

end
end GinibrePoincare
