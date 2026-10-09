module

public import GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianBracket
public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyCrossBracket

@[expose] public section

/-! All real coordinates and mixed brackets of the actual configuration noise. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def ginibreConfigurationBrownianRealCoordinate {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (p : Fin n × Fin 2)
    (t : ℝ≥0) (ω : Ω) : ℝ :=
  if p.2 = 0 then (ginibreConfigurationBrownianNoise n B α ω t p.1).re
    else (ginibreConfigurationBrownianNoise n B α ω t p.1).im

theorem ginibreConfigurationBrownianRealCoordinate_eq {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (p : Fin n × Fin 2)
    (t : ℝ≥0) (ω : Ω) :
    ginibreConfigurationBrownianRealCoordinate n B α p t ω =
      Real.sqrt (2*α/(n : ℝ)^2)*B p t ω := by
  rcases p with ⟨j, k⟩
  fin_cases k <;> simp [ginibreConfigurationBrownianRealCoordinate, ginibreConfigurationBrownianNoise,
    Complex.mul_re, Complex.mul_im]

theorem ginibreConfigurationBrownianRealCoordinate_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (p : Fin n × Fin 2) :
    Martingale (ginibreConfigurationBrownianRealCoordinate n B α p)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_martingale B P hB hind p).smul
    (Real.sqrt (2*α/(n : ℝ)^2))
  convert! h using 1
  funext t ω
  simp only [ginibreConfigurationBrownianRealCoordinate_eq, Pi.smul_apply, smul_eq_mul]

theorem ginibreConfigurationBrownianRealCoordinate_cross_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (p q : Fin n × Fin 2) (hpq : p ≠ q) :
    Martingale (fun t ω => ginibreConfigurationBrownianRealCoordinate n B α p t ω*
      ginibreConfigurationBrownianRealCoordinate n B α q t ω)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_cross_martingale B P hB hind p q hpq).smul
    ((Real.sqrt (2*α/(n : ℝ)^2))^2)
  convert! h using 1
  funext t ω
  simp only [ginibreConfigurationBrownianRealCoordinate_eq, Pi.smul_apply, smul_eq_mul]
  ring

theorem ginibreConfigurationBrownianRealCoordinate_square_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0) (p : Fin n × Fin 2) :
    Martingale (fun t ω => (ginibreConfigurationBrownianRealCoordinate n B α p t ω)^2-
      (2*(α : ℝ)/(n : ℝ)^2)*(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_square_martingale B P hB hind p).smul
    (2*(α : ℝ)/(n : ℝ)^2)
  have hσ : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 :=
    Real.sq_sqrt (div_nonneg (by positivity) (sq_nonneg _))
  convert! h using 1
  funext t ω
  simp only [ginibreConfigurationBrownianRealCoordinate_eq, mul_pow, hσ, Pi.smul_apply, smul_eq_mul]
  ring

end
end GinibrePoincare
