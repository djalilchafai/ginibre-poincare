module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyBracket
public import GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianMartingale

@[expose] public section

/-! Exact square-minus-variance martingales for the paper's configuration noise. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreConfigurationBrownianNoise_real_square_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).re^2-
      (2*(α : ℝ)/(n : ℝ)^2)*(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_square_martingale B P hB hind (j,0)).smul
    (2*(α : ℝ)/(n : ℝ)^2)
  have hσ : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  convert! h using 1
  funext t ω
  have he : (ginibreConfigurationBrownianNoise n B α ω t j).re =
      Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*B (j,0) t ω := by
    simp [ginibreConfigurationBrownianNoise, Complex.mul_re]
  rw [he, mul_pow, hσ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem ginibreConfigurationBrownianNoise_imag_square_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).im^2-
      (2*(α : ℝ)/(n : ℝ)^2)*(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_square_martingale B P hB hind (j,1)).smul
    (2*(α : ℝ)/(n : ℝ)^2)
  have hσ : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  convert! h using 1
  funext t ω
  have he : (ginibreConfigurationBrownianNoise n B α ω t j).im =
      Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*B (j,1) t ω := by
    simp [ginibreConfigurationBrownianNoise, Complex.mul_im]
  rw [he, mul_pow, hσ]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end
end GinibrePoincare
