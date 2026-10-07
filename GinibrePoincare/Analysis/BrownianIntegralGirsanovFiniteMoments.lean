module

public import GinibrePoincare.Analysis.BrownianIntegralGirsanovFinite

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem brownianPredictableGaussianDensity_lintegral_step_sq
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hh : ∀ k, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (N : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (brownianPredictableGaussianDensity (B j) h τ (N+1) ω)^2 ∂P)=
      ∫⁻ ω, ENNReal.ofReal (brownianPredictableGaussianDensity (B j) h τ N ω)^2*
        ENNReal.ofReal (Real.exp ((h N ω)^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) ∂P := by
  let Y := fun ω => (h N ω,brownianPredictableGaussianDensity (B j) h τ N ω)
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
  have he := gaussianPredictableTilt_lintegral_sq P Y X hYa.aemeasurable
    (τ (N+1)-τ N) hX hi Prod.fst (fun y : ℝ×ℝ => ENNReal.ofReal y.2^2)
    measurable_fst ((ENNReal.measurable_ofReal.comp measurable_snd).pow_const 2)
  simp only [Y,Prod.fst,Prod.snd,X] at he
  simp_rw [brownianPredictableGaussianDensity_succ,
    ENNReal.ofReal_mul (brownianPredictableGaussianDensity_pos (B j) h τ N _).le,mul_pow]
  exact he

/-- Genuine uniform second-moment bound for the finite predictable Gaussian
Radon--Nikodym densities of the original Brownian family. -/
theorem brownianPredictableGaussianDensity_lintegral_sq_le
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (h : ℕ → Ω → ℝ) (τ : ℕ → ℝ≥0) (hτ : Monotone τ) (h0 : τ 0=0)
    (hh : ∀ k, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (h k))
    (C : ℝ) (hC : 0≤C) (hb : ∀ k ω, ‖h k ω‖≤C) (N : ℕ) :
    (∫⁻ ω, ENNReal.ofReal (brownianPredictableGaussianDensity (B j) h τ N ω)^2 ∂P) ≤
      ENNReal.ofReal (Real.exp (C^2*(τ N : ℝ))) := by
  induction N with
  | zero => simp [brownianPredictableGaussianDensity,h0]
  | succ N ih =>
    rw [brownianPredictableGaussianDensity_lintegral_step_sq B P hB hind j h τ hτ hh N]
    have he (ω : Ω) : ENNReal.ofReal (Real.exp ((h N ω)^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) ≤
        ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right _ (NNReal.coe_nonneg _)
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg _) (hb N ω) 2
    calc
      _ ≤ ∫⁻ ω, ENNReal.ofReal (brownianPredictableGaussianDensity (B j) h τ N ω)^2*
          ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) ∂P :=
        lintegral_mono (fun ω => mul_le_mul' le_rfl (he ω))
      _ = (∫⁻ ω, ENNReal.ofReal (brownianPredictableGaussianDensity (B j) h τ N ω)^2 ∂P)*
          ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) := by
        rw [lintegral_mul_const _ (by
          have hm := (brownianPredictableGaussianDensity_measurable_at B P hB j h τ hτ hh N).mono
            ((ginibreBrownianAugmentedFiltration B P hB).le _) le_rfl
          exact (ENNReal.measurable_ofReal.comp hm).pow_const 2)]
      _ ≤ ENNReal.ofReal (Real.exp (C^2*(τ N : ℝ)))*
          ENNReal.ofReal (Real.exp (C^2*((τ (N+1)-τ N : ℝ≥0) : ℝ))) := mul_le_mul' ih le_rfl
      _ = ENNReal.ofReal (Real.exp (C^2*(τ (N+1) : ℝ))) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le,← Real.exp_add,
          NNReal.coe_sub (hτ (Nat.le_succ N))]
        congr 2
        ring

end
end GinibrePoincare
