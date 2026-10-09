module

public import GinibrePoincare.Analysis.GinibreDrivenPathMeasurableLocalFlow
public import GinibrePoincare.Analysis.GinibreStochasticLocalExistence
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! Actual Brownian configuration noise as a measurable continuous-path random element. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibre_measurable_continuousMap_of_evaluations
    {Ω T E : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace T] [TopologicalSpace.SeparableSpace T] [Nonempty T]
    [TopologicalSpace E] [SecondCountableTopology E] [T2Space E] [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(T, E)] [BorelSpace C(T, E)] [PolishSpace C(T, E)]
    (F : Ω → C(T, E)) (hF : ∀ t, Measurable (fun ω => F ω t)) : Measurable F := by
  let d := TopologicalSpace.denseSeq T
  let e : C(T, E) → ℕ → E := fun f k => f (d k)
  have he : Continuous e := continuous_pi (fun k => continuous_eval_const (d k))
  have hinj : Function.Injective e := by
    intro f g hfg
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq T).equalizer f.continuous g.continuous hfg
  apply he.measurableEmbedding hinj |>.measurable_comp_iff.mp
  apply measurable_pi_lambda
  intro k
  exact hF (d k)

def ginibreConfigurationBrownianContinuousPath {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω) :
    C(Icc (-1 : ℝ) 1, Configuration n) :=
  ContinuousMap.mkD (fun t => ginibreConfigurationBrownianNoise n B α ω t) 0

theorem ginibreConfigurationBrownianContinuousPath_ae {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    ∀ᵐ ω ∂P, ∀ t : Icc (-1 : ℝ) 1,
      ginibreConfigurationBrownianContinuousPath n B α ω t = ginibreConfigurationBrownianNoise n B α ω t := by
  filter_upwards [ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω
  intro t
  have hc : Continuous (fun t : Icc (-1 : ℝ) 1 => ginibreConfigurationBrownianNoise n B α ω t) := hω.1.comp continuous_subtype_val
  simp [ginibreConfigurationBrownianContinuousPath, ContinuousMap.mkD, hc]

theorem ginibreConfigurationBrownianContinuousPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ) :
    @Measurable _ _ _ (borel C(Icc (-1 : ℝ) 1, Configuration n))
      (ginibreConfigurationBrownianContinuousPath n B α) := by
  letI : Nonempty (Icc (-1 : ℝ) 1) := ⟨⟨0, by norm_num⟩⟩
  letI : MeasurableSpace C(Icc (-1 : ℝ) 1, Configuration n) := borel _
  letI : BorelSpace C(Icc (-1 : ℝ) 1, Configuration n) := ⟨rfl⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  have hNoise : Measurable (fun ω => ginibreConfigurationBrownianNoise n B α ω t) := by
    apply measurable_pi_lambda
    intro j
    exact (((aemeasurable_iff_measurable.mp ((hB (j, 0)).aemeasurable t.val.toNNReal)).complex_ofReal).add
      (measurable_const.mul ((aemeasurable_iff_measurable.mp
        ((hB (j, 1)).aemeasurable t.val.toNNReal)).complex_ofReal))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  exact hNoise.aemeasurable.congr (by
    filter_upwards [ginibreConfigurationBrownianContinuousPath_ae n B P hB α] with ω hω
    exact (hω t).symm)

end
end GinibrePoincare
