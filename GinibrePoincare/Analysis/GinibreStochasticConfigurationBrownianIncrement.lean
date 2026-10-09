module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyPast
public import GinibrePoincare.Analysis.GinibreStochasticLocalExistence

@[expose] public section

/-! The actual general-particle Brownian noise has fresh Gaussian independent increments. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def ginibreConfigurationBrownianEmbedding (n : ℕ) (α : ℝ) :
    ((Fin n × Fin 2) → ℝ) → Configuration n := fun v j =>
  Real.sqrt (2*α/(n : ℝ)^2) • ((v (j, 0) : ℂ)+Complex.I*(v (j, 1) : ℂ))

theorem ginibreConfigurationBrownianEmbedding_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreConfigurationBrownianEmbedding n α) := by
  unfold ginibreConfigurationBrownianEmbedding
  fun_prop

def ginibreConfigurationBrownianIncrementLaw (n : ℕ) (α : ℝ) (t : ℝ≥0) : Measure (Configuration n) :=
  (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 t)).map (ginibreConfigurationBrownianEmbedding n α)

instance ginibreConfigurationBrownianIncrementLaw_isProbabilityMeasure (n : ℕ) (α : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (ginibreConfigurationBrownianIncrementLaw n α t) :=
  (by unfold ginibreConfigurationBrownianIncrementLaw; infer_instance)

theorem ginibreConfigurationBrownianNoise_increment_eq {Ω : Type*}
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (s t : ℝ≥0) (ω : Ω) :
    ginibreConfigurationBrownianNoise n B α ω (s+t)-ginibreConfigurationBrownianNoise n B α ω s =
      ginibreConfigurationBrownianEmbedding n α (fun i => B i (s+t) ω-B i s ω) := by
  ext j
  simp only [ginibreConfigurationBrownianNoise, ginibreConfigurationBrownianEmbedding,
    ← NNReal.coe_add, Real.toNNReal_coe, Pi.sub_apply, smul_sub, Complex.ofReal_sub]
  rw [← smul_sub]
  congr 1
  ring

theorem ginibreConfigurationBrownianNoise_increment_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (s t : ℝ≥0) :
    HasLaw (fun ω => ginibreConfigurationBrownianNoise n B α ω (s+t)-ginibreConfigurationBrownianNoise n B α ω s)
      (ginibreConfigurationBrownianIncrementLaw n α t) P := by
  have hE : HasLaw (ginibreConfigurationBrownianEmbedding n α)
      (ginibreConfigurationBrownianIncrementLaw n α t) (Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 t)) :=
    ⟨(ginibreConfigurationBrownianEmbedding_measurable n α).aemeasurable, rfl⟩
  have h := hE.comp (ginibreBrownian_family_increment_hasLaw B P hB hind s t)
  simpa only [Function.comp_def, id_eq, ginibreConfigurationBrownianNoise_increment_eq] using h

theorem ginibreConfigurationBrownianNoise_increment_independent_past {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ) (s t : ℝ≥0) :
    IndepFun (fun ω => ginibreConfigurationBrownianNoise n B α ω (s+t)-ginibreConfigurationBrownianNoise n B α ω s)
      (fun ω (p : (Fin n × Fin 2) × Set.Iic s) => B p.1 p.2 ω) P := by
  have h := (ginibreBrownian_family_increment_independent_past B P hB hind s t).comp
    (ginibreConfigurationBrownianEmbedding_measurable n α) measurable_id
  simpa only [Function.comp_def, id_eq, ginibreConfigurationBrownianNoise_increment_eq] using h

end
end GinibrePoincare
