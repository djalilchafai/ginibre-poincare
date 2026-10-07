module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianShifted

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- The process defined by the actual shifted left-sum limits of an adapted
unit field is genuinely Brownian. Gaussian laws and joint increment
independence are derived from the original coordinate Brownian family. -/
theorem brownianUnitField_actual_integral_isBrownian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ s, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ (u s))
    (hunit : ∀ s ω, ‖u s ω‖ = 1) (i : ι) (M : ℝ≥0 → Ω → ℝ)
    (hM : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) M)
    (hM0 : M 0 =ᵐ[P] (fun _ => 0))
    (hMC : ∀ᵐ ω ∂P, Continuous (fun t => M t ω))
    (hlim : ∀ s t, TendstoInMeasure P
      (fun n => brownianUnitShiftedUniformSum B u s t (n+1)) atTop
        (fun ω => M (s+t) ω-M s ω)) :
    IsBrownianReal M P := by
  have hlaw : ∀ t, HasLaw (M t) (gaussianReal 0 t) P := by
    intro t
    have hh := (brownianUnitShiftedUniformSum_limit_gaussian_independent B P hB hind
      u hu hunit i 0 t _ (hlim 0 t) (fun _ => (0 : ℝ)) measurable_const).1
    apply hh.congr
    filter_upwards [hM0] with ω hω
    simp only [zero_add,hω,sub_zero]
  have hincr : HasIndepIncrements M P := by
    intro n τ hτ
    let τe : ℕ → ℝ≥0 := fun k => τ ⟨min k n,Nat.lt_succ_of_le (min_le_right _ _)⟩
    have hτe : Monotone τe := by
      intro a b hab
      apply hτ
      exact min_le_min_right n hab
    let Z : ℕ → Ω → ℝ := fun k ω => M (τe (k+1)) ω-M (τe k) ω
    have hZm : ∀ k, @Measurable Ω ℝ
        (ginibreBrownianAugmentedFiltration B P hB (τe (k+1))) _ (Z k) := by
      intro k
      exact ((hM _).measurable).sub (((hM _).measurable).mono
        ((ginibreBrownianAugmentedFiltration B P hB).mono (hτe (Nat.le_succ k))) le_rfl)
    have hi : iIndepFun Z P := by
      apply chronologicalFresh_iIndepFun P
        (sampledMartingaleFiltration (ginibreBrownianAugmentedFiltration B P hB) τe hτe) Z hZm
      intro k Y hY
      have hh := (brownianUnitShiftedUniformSum_limit_gaussian_independent B P hB hind
        u hu hunit i (τe k) (τe (k+1)-τe k) _ (hlim _ _) Y hY).2
      simpa only [add_tsub_cancel_of_le (hτe (Nat.le_succ k)),Z] using hh
    have hf := hi.precomp (g := fun k : Fin n => k.val) Fin.val_injective
    convert hf using 1
    funext k ω
    simp only [Z,τe,min_eq_left (Nat.succ_le_of_lt k.is_lt),min_eq_left k.is_lt.le]
    rfl
  exact ⟨hincr.isPreBrownianReal_of_hasLaw hlaw,hMC⟩

end
end GinibrePoincare
