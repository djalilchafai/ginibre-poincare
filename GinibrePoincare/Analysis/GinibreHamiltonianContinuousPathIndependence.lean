module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUContinuousReversal

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibre_iIndepFun_continuousMap_of_raw_paths
    {Ω ι D E : Type*} [MeasurableSpace Ω] [TopologicalSpace D]
    [TopologicalSpace.SeparableSpace D] [Nonempty D]
    [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace C(D, E)] [BorelSpace C(D, E)] [PolishSpace C(D, E)] [Nonempty C(D, E)]
    (P : Measure Ω) (X : ι → Ω → C(D, E))
    (h : iIndepFun (fun i ω t => X i ω t) P) : iIndepFun X P := by
  let d := TopologicalSpace.denseSeq D
  let e : C(D, E) → ℕ → E := fun x k => x (d k)
  have he : MeasurableEmbedding e :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y hxy
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq D).equalizer x.continuous y.continuous hxy)
  have hd : Measurable (fun x : D → E => fun k => x (d k)) :=
    Measurable.of_eval (fun k => measurable_pi_apply (d k))
  have hi := h.comp (fun _ => fun x : D → E => fun k => x (d k)) (fun _ => hd)
  have hj := hi.comp (fun _ => he.invFun) (fun _ => he.measurable_invFun)
  convert hj using 1
  funext i ω
  exact (he.leftInverse_invFun (X i ω)).symm

local instance ginibreScalarBrownianCMMeasurable : MeasurableSpace C(ℝ≥0, ℝ) := borel _
local instance ginibreScalarBrownianCMBorel : BorelSpace C(ℝ≥0, ℝ) := ⟨rfl⟩

def ginibreScalarBrownianDenseEvaluation : C(ℝ≥0, ℝ) → ℕ → ℝ :=
  fun x k => x (TopologicalSpace.denseSeq ℝ≥0 k)

theorem ginibreScalarBrownianDenseEvaluation_embedding :
    MeasurableEmbedding ginibreScalarBrownianDenseEvaluation :=
  (continuous_pi (fun k => continuous_eval_const (TopologicalSpace.denseSeq ℝ≥0 k))).measurableEmbedding (by
    intro x y hxy
    apply DFunLike.coe_injective
    exact (TopologicalSpace.denseRange_denseSeq ℝ≥0).equalizer x.continuous y.continuous hxy)

/-- A globally measurable normalization from the raw product path space. -/
def ginibreScalarBrownianNormalize (x : ℝ≥0 → ℝ) : C(ℝ≥0, ℝ) :=
  ginibreScalarBrownianDenseEvaluation_embedding.invFun
    (fun k => x (TopologicalSpace.denseSeq ℝ≥0 k))

theorem ginibreScalarBrownianNormalize_measurable : Measurable ginibreScalarBrownianNormalize :=
  ginibreScalarBrownianDenseEvaluation_embedding.measurable_invFun.comp
    (Measurable.of_eval (fun k => measurable_pi_apply (TopologicalSpace.denseSeq ℝ≥0 k)))

theorem ginibreScalarBrownianNormalize_continuous (x : ℝ≥0 → ℝ) (hx : Continuous x) :
    ∀ t, ginibreScalarBrownianNormalize x t = x t := by
  have he := ginibreScalarBrownianDenseEvaluation_embedding.leftInverse_invFun (⟨x, hx⟩ : C(ℝ≥0, ℝ))
  exact fun t => congrArg (fun y : C(ℝ≥0, ℝ) => y t) he

#print axioms ginibreScalarBrownianNormalize_measurable
#print axioms ginibreScalarBrownianNormalize_continuous
#print axioms ginibre_iIndepFun_continuousMap_of_raw_paths
end
end GinibrePoincare
