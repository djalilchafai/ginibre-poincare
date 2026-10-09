module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianPast
public import GinibrePoincare.Analysis.BrownianIntegralGaussianIndependenceLimit

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Original unit-field coordinate sums on the actual shifted interval. -/
def brownianUnitShiftedUniformSum {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (s t : ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ j, ∑ k ∈ Finset.range N, u (s+itoUniformNNTime t N k) ω j *
    (B j (s+itoUniformNNTime t N (k+1)) ω-B j (s+itoUniformNNTime t N k) ω)

theorem monotoneGrid_duration_sum_from_start (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (n : ℕ) :
    (∑ k ∈ Finset.range n, (τ (k+1)-τ k)) = τ n-τ 0 := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum, NNReal.coe_sub (hτ (Nat.zero_le n))]
  simp_rw [NNReal.coe_sub (hτ (Nat.le_succ _))]
  exact Finset.sum_range_sub (fun k => (τ k : ℝ)) n

theorem brownianUnitShiftedUniformSum_eq_prefix {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (s t : ℝ≥0) (N : ℕ) :
    brownianUnitShiftedUniformSum B u s t N =
      brownianUnitGridPrefix B (fun k => u (s+itoUniformNNTime t N k))
        (fun k => s+itoUniformNNTime t N k) N := by
  funext ω
  have hτ : Monotone (fun k => s+itoUniformNNTime t N k) :=
    monotone_const.add (itoUniformNNTime_mono t N)
  unfold brownianUnitShiftedUniformSum brownianUnitGridPrefix
  simp_rw [brownianUnitGridInnovation_eq B _ _ hτ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  simp [PiLp.inner_apply, mul_comm]

/-- Exact shifted Gaussian law and independence of the entire actual initial
completed past, before taking any stochastic integral limit. -/
theorem brownianUnitShiftedUniformSum_gaussian_independent
    {Ω ι A : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ s, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ (u s))
    (hunit : ∀ s ω, ‖u s ω‖ = 1) (i : ι) (s t : ℝ≥0) (N : ℕ) (hN : 0 < N)
    (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) :
    HasLaw (brownianUnitShiftedUniformSum B u s t N) (gaussianReal 0 t) P ∧
      IndepFun Y (brownianUnitShiftedUniformSum B u s t N) P := by
  let τ := fun k => s+itoUniformNNTime t N k
  have hτ : Monotone τ := monotone_const.add (itoUniformNNTime_mono t N)
  have h0 : τ 0 = s := by simp [τ, itoUniformNNTime, itoUniformTime]
  have hEnd : τ N = s+t := by rw [show τ N=s+itoUniformNNTime t N N from rfl, itoUniformNNTime_end t N hN]
  have hl := brownianUnitGridPrefix_gaussian B P hB hind (fun k => u (τ k)) τ hτ
    (fun k => hu (τ k)) (fun k => hunit (τ k)) i N
  have hi := brownianUnitGridPrefix_independent_past B P hB hind (fun k => u (τ k)) τ hτ
    (fun k => hu (τ k)) (fun k => hunit (τ k)) i Y (by rwa [h0]) N
  rw [monotoneGrid_duration_sum_from_start τ hτ N, hEnd, h0, add_tsub_cancel_left] at hl
  simpa only [brownianUnitShiftedUniformSum_eq_prefix] using ⟨hl, hi⟩

/-- The genuine probability limit of the original shifted sums has its exact
Gaussian law and is independent of any original completed-past variable. -/
theorem brownianUnitShiftedUniformSum_limit_gaussian_independent
    {Ω ι A : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ s, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ (u s))
    (hunit : ∀ s ω, ‖u s ω‖ = 1) (i : ι) (s t : ℝ≥0) (L : Ω → ℝ)
    (hL : TendstoInMeasure P (fun n => brownianUnitShiftedUniformSum B u s t (n+1)) atTop L)
    (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y) :
    HasLaw L (gaussianReal 0 t) P ∧ IndepFun Y L P := by
  have hseq := fun n => brownianUnitShiftedUniformSum_gaussian_independent B P hB hind
    u hu hunit i s t (n+1) (Nat.succ_pos n) Y hY
  exact ⟨actualConstantLaw_of_tendstoInMeasure P (gaussianReal 0 t) _ (fun n => (hseq n).1) L hL,
    actualConstantLaw_independent_of_limit P (gaussianReal 0 t) _ (fun n => (hseq n).1) L hL Y
      (hY.mono ((ginibreBrownianAugmentedFiltration B P hB).le s) le_rfl) (fun n => (hseq n).2)⟩

end
end GinibrePoincare
