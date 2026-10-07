module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianChronology
public import GinibrePoincare.Analysis.GinibreBrownianIntegralUniformSums

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual finite innovation vector has the literal product Gaussian law. -/
theorem brownianUnitGridInnovation_product_law
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k))
    (hunit : ∀ k ω, ‖u k ω‖ = 1) (i : ι) (N : ℕ) :
    HasLaw (fun ω (k : Fin N) => brownianUnitGridInnovation B u τ k ω)
      (Measure.pi (fun k : Fin N => gaussianReal 0 (τ (k.val+1)-τ k))) P := by
  have hl : ∀ k : Fin N, HasLaw (brownianUnitGridInnovation B u τ k)
      (gaussianReal 0 (τ (k.val+1)-τ k)) P := fun k =>
    (brownianUnitGridInnovation_gaussian_independent B P hB hind u τ hu hunit k
      (fun _ => (0 : ℝ)) measurable_const i).1
  have hi := (brownianUnitGridInnovation_iIndepFun B P hB hind u τ hτ hu hunit i).precomp
    (g := fun k : Fin N => k.val) Fin.val_injective
  exact (iIndepFun_iff_hasLaw_pi_pi hl).mp hi

/-- The sum of the actual grid interval lengths equals the endpoint horizon. -/
theorem monotoneGrid_duration_sum (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (h0 : τ 0 = 0) (n : ℕ) :
    (∑ k ∈ Finset.range n, (τ (k+1)-τ k)) = τ n := by
  apply NNReal.coe_injective
  simp only [NNReal.coe_sum]
  simp_rw [NNReal.coe_sub (hτ (Nat.le_succ _))]
  rw [Finset.sum_range_sub (fun k => (τ k : ℝ)) n,h0]
  simp

/-- Genuine Gaussian endpoint law for the literal sum of coordinate Brownian
left sums with an actual adapted unit vector field. -/
theorem brownianUnitField_uniform_sum_gaussian
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℝ≥0 → Ω → EuclideanSpace ℝ ι)
    (hu : ∀ s, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB s) _ (u s))
    (hunit : ∀ s ω, ‖u s ω‖ = 1) (i : ι) (T : ℝ≥0) (N : ℕ) (hN : 0 < N) :
    HasLaw (fun ω => ∑ j, brownianUniformLeftSum (B j) (fun s ω => u s ω j) T N ω)
      (gaussianReal 0 T) P := by
  let τ := itoUniformNNTime T N
  have hτ : Monotone τ := itoUniformNNTime_mono T N
  have hzero : τ 0 = 0 := by simp [τ,itoUniformNNTime,itoUniformTime]
  have hl := brownianUnitGridPrefix_gaussian B P hB hind (fun k => u (τ k)) τ hτ
    (fun k => hu (τ k)) (fun k => hunit (τ k)) i N
  have hEnd : τ N = T := itoUniformNNTime_end T N hN
  rw [monotoneGrid_duration_sum τ hτ hzero N,hEnd] at hl
  have he : brownianUnitGridPrefix B (fun k => u (τ k)) τ N =
      (fun ω => ∑ j, brownianUniformLeftSum (B j) (fun s ω => u s ω j) T N ω) := by
    funext ω
    unfold brownianUnitGridPrefix brownianUniformLeftSum
    simp_rw [brownianUnitGridInnovation_eq B (fun k => u (τ k)) τ hτ]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    simp [τ,PiLp.inner_apply,Real.inner_apply,mul_comm]
  rwa [he] at hl

end
end GinibrePoincare
