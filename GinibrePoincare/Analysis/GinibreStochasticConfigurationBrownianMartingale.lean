module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyMartingale
public import GinibrePoincare.Analysis.GinibreStochasticConfigurationBrownianIncrement

@[expose] public section

/-! The actual normalized n-particle noise is adapted and has martingale coordinates. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreConfigurationBrownianNoise_real_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).re)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_martingale B P hB hind (j,0)).smul
    (Real.sqrt (2*α/(n : ℝ)^2))
  convert! h using 1
  funext t ω
  simp [ginibreConfigurationBrownianNoise, Pi.smul_apply, smul_eq_mul, Complex.mul_re]

theorem ginibreConfigurationBrownianNoise_imag_martingale {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (j : Fin n) :
    Martingale (fun (t : ℝ≥0) ω => (ginibreConfigurationBrownianNoise n B α ω t j).im)
      (ginibreBrownianFamilyFiltration B P hB) P := by
  have h := (ginibreBrownianFamilyFiltration_coordinate_martingale B P hB hind (j,1)).smul
    (Real.sqrt (2*α/(n : ℝ)^2))
  convert! h using 1
  funext t ω
  simp [ginibreConfigurationBrownianNoise, Pi.smul_apply, smul_eq_mul, Complex.mul_im]

theorem ginibreConfigurationBrownianNoise_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (α : ℝ) :
    StronglyAdapted (ginibreBrownianFamilyFiltration B P hB)
      (fun t ω => ginibreConfigurationBrownianNoise n B α ω t) := by
  intro s
  have hPast : @Measurable Ω ((Fin n × Fin 2) × Set.Iic s → ℝ)
      (ginibreBrownianFamilyPastSpace B s) inferInstance
      (fun ω p => B p.1 p.2 ω) := Measurable.of_comap_le le_rfl
  have hEval : Measurable (fun p : (Fin n × Fin 2) × Set.Iic s → ℝ =>
      fun i => p (i, ⟨s, by change s ≤ s; exact le_rfl⟩)) := by fun_prop
  have h := ((ginibreConfigurationBrownianEmbedding_measurable n α).comp hEval).comp hPast
  apply Measurable.stronglyMeasurable
  convert! h using 1
  funext ω j
  simp only [Function.comp_apply, ginibreConfigurationBrownianNoise,
    ginibreConfigurationBrownianEmbedding, Real.toNNReal_coe]

end
end GinibrePoincare
