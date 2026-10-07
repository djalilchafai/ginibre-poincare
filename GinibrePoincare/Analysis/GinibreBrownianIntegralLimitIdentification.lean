module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralLimitAdaptation

@[expose] public section

/-! The actual continuous subsequence limit is the genuine L² integral representative. -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem actualL2Limit_eq_ae_of_subsequence_tendsto {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P] (S : ℕ → Ω → ℝ) (hs : ∀ n, MemLp (S n) 2 P)
    (I : Lp ℝ 2 P) (hlim : Tendsto (fun n => (hs n).toLp (S n)) atTop (𝓝 I))
    (s : ℕ → ℕ) (hmono : StrictMono s) (J : Ω → ℝ)
    (hJ : ∀ᵐ ω ∂P, Tendsto (fun n => S (s n) ω) atTop (𝓝 (J ω))) :
    J =ᵐ[P] (fun ω => I ω) := by
  have hL := tendstoInMeasure_of_tendsto_Lp (hlim.comp hmono.tendsto_atTop)
  have hI : TendstoInMeasure P (fun n => S (s n)) atTop (fun ω => I ω) :=
    hL.congr (fun n => (hs (s n)).coeFn_toLp) EventuallyEq.rfl
  have hj := tendstoInMeasure_of_tendsto_ae (fun n => (hs (s n)).aestronglyMeasurable) hJ
  exact tendstoInMeasure_ae_unique hj hI

end
end GinibrePoincare
