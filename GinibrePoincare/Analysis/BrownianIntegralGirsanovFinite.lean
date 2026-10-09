module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltPredictable
public import GinibrePoincare.Analysis.GinibreBrownianIntegralBaseMartingale

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

def brownianPredictableGaussianDensity {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ k ∈ Finset.range N,
    (h k ω*(B (τ (k+1)) ω-B (τ k) ω)-(h k ω)^2*((τ (k+1)-τ k : ℝ≥0) : ℝ)/2))

theorem brownianPredictableGaussianDensity_zero {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (ω : Ω) :
    brownianPredictableGaussianDensity B h τ 0 ω=1 := by
  simp [brownianPredictableGaussianDensity]

theorem brownianPredictableGaussianDensity_pos {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) :
    0<brownianPredictableGaussianDensity B h τ N ω := Real.exp_pos _

theorem brownianPredictableGaussianDensity_succ {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (N : ℕ) (ω : Ω) :
    brownianPredictableGaussianDensity B h τ (N+1) ω =
      brownianPredictableGaussianDensity B h τ N ω*
        gaussianExponentialTilt (h N ω) (τ (N+1)-τ N) (B (τ (N+1)) ω-B (τ N) ω) := by
  simp only [brownianPredictableGaussianDensity, Finset.sum_range_succ, Real.exp_add,
    gaussianExponentialTilt]

theorem brownianPredictableGaussianDensity_measurable_at
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (j : ι)
    (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ N)) _
      (brownianPredictableGaussianDensity (B j) h τ N) := by
  induction N with
  | zero =>
    have he : brownianPredictableGaussianDensity (B j) h τ 0=(fun _ => 1) :=
      funext (brownianPredictableGaussianDensity_zero (B j) h τ)
    rw [he]
    exact measurable_const
  | succ N ih =>
    have hp := ih.mono ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ (Nat.le_succ N))) le_rfl
    have hhm := (hh N).mono ((ginibreBrownianAugmentedFiltration B P hB).mono (hτ (Nat.le_succ N))) le_rfl
    have hXm := (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (N+1)) _ le_rfl j).sub
      (ginibreBrownian_augmented_coordinate_measurable_at B P hB (τ (N+1)) _ (hτ (Nat.le_succ N)) j)
    have hm := hp.mul (((hhm.mul hXm).sub ((hhm.pow_const 2).mul_const
      (((τ (N+1)-τ N : ℝ≥0) : ℝ)/2))).exp)
    convert hm using 1
    funext ω
    rw [brownianPredictableGaussianDensity_succ]
    unfold gaussianExponentialTilt
    simp only [Pi.mul_apply, Pi.sub_apply]
    congr 2
    ring

/-- Normalization of the actual finite predictable Gaussian Radon--Nikodym
weight, derived solely from original-family fresh Gaussian increments. -/
theorem brownianPredictableGaussianDensity_lintegral
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) : (∫⁻ ω, ENNReal.ofReal (brownianPredictableGaussianDensity (B j) h τ N ω) ∂P)=1 := by
  induction N with
  | zero => simp [brownianPredictableGaussianDensity]
  | succ N ih =>
    let Y := fun ω => (h N ω, brownianPredictableGaussianDensity (B j) h τ N ω)
    have hY : @Measurable Ω (ℝ×ℝ) (ginibreBrownianAugmentedFiltration B P hB (τ N)) _ Y :=
      (hh N).prodMk (brownianPredictableGaussianDensity_measurable_at B P hB j h τ hτ hh N)
    have hYa := hY.mono ((ginibreBrownianAugmentedFiltration B P hB).le (τ N)) le_rfl
    let X := fun ω => B j (τ (N+1)) ω-B j (τ N) ω
    have hX : HasLaw X (gaussianReal 0 (τ (N+1)-τ N)) P :=
      ginibreBrownian_increment_hasLaw (B j) P (hB j) (τ N) (τ (N+1)) (hτ (Nat.le_succ N))
    have hi : IndepFun Y X P := by
      have hi := (ginibreBrownian_augmented_coordinate_increment_independent B P hB hind
        (τ N) (τ (N+1)-τ N) j Y hY).symm
      simpa only [add_tsub_cancel_of_le (hτ (Nat.le_succ N))] using hi
    have he := gaussianPredictableTilt_lintegral P Y X hYa.aemeasurable
      (τ (N+1)-τ N) hX hi Prod.fst (fun y : ℝ×ℝ => ENNReal.ofReal y.2)
      measurable_fst (ENNReal.measurable_ofReal.comp measurable_snd)
    simp only [Y, Prod.fst, Prod.snd, X] at he
    simp_rw [brownianPredictableGaussianDensity_succ,
      ENNReal.ofReal_mul (brownianPredictableGaussianDensity_pos (B j) h τ N _).le]
    exact he.trans ih

end
end GinibrePoincare
