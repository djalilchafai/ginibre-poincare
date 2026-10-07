module

public import GinibrePoincare.Analysis.BrownianOrthogonalFuturePath
public import GinibrePoincare.Analysis.BrownianOrthogonalContinuousNoise

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem indepFun_continuousMap_left_of_path_independence {Ω E A : Type*}
    [MeasurableSpace Ω] [TopologicalSpace E] [SecondCountableTopology E] [T2Space E]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace A]
    [MeasurableSpace C(ℝ,E)] [BorelSpace C(ℝ,E)] [PolishSpace C(ℝ,E)]
    (P : Measure Ω) (X : Ω → C(ℝ,E)) (Y : Ω → A)
    (hi : IndepFun (fun ω t => X ω t) Y P) : IndepFun X Y P := by
  let d := TopologicalSpace.denseSeq ℝ
  let f : C(ℝ,E) → ℕ → E := fun x k => x (d k)
  have hf : MeasurableEmbedding f :=
    (continuous_pi (fun k => continuous_eval_const (d k))).measurableEmbedding (by
      intro x y h
      apply DFunLike.coe_injective
      exact (TopologicalSpace.denseRange_denseSeq ℝ).equalizer x.continuous y.continuous h)
  have hE : Measurable (fun x : ℝ → E => fun k : ℕ => x (d k)) := by
    apply measurable_pi_lambda
    intro k
    exact measurable_pi_apply (d k)
  exact indepFun_of_measurable_embeddings P X Y f id hf .id (hi.comp hE measurable_id)

/-- The actual shifted normalized continuous configuration Brownian noise is
independent of every actual completed-past measurable state. -/
theorem brownianFamily_future_continuous_noise_independent_augmented_variable
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (s : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) s) _ Y) :
    IndepFun (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α) Y P := by
  letI : MeasurableSpace C(ℝ,Configuration n) := borel _
  letI : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
  let N := ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  let H : ((Fin n × Fin 2) → ℝ≥0 → ℝ) → ℝ → Configuration n :=
    fun p t j => Real.sqrt (2*α/(n : ℝ)^2) •
      ((p (j,0) t.toNNReal : ℂ)+Complex.I*(p (j,1) t.toNNReal : ℂ))
  have hH : Measurable H := by
    apply measurable_pi_lambda
    intro t
    apply measurable_pi_lambda
    intro j
    exact ((((measurable_pi_apply t.toNNReal).comp (measurable_pi_apply (j,0))).complex_ofReal).add
      (measurable_const.mul (((measurable_pi_apply t.toNNReal).comp
        (measurable_pi_apply (j,1))).complex_ofReal))).const_smul (Real.sqrt (2*α/(n : ℝ)^2))
  have hfresh := brownianFamily_future_independent_augmented_variable B P
    (fun i => (hB i).toIsPreBrownianReal) hind s Y hY
  have hraw := hfresh.comp hH measurable_id
  have hshift := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  have heq : (fun ω => H (fun i t => brownianFamilyShift B s i t ω)) =ᵐ[P]
      (fun ω t => (N ω).val t) := by
    filter_upwards [ginibreBrownianFullContinuousNoise_ae n (brownianFamilyShift B s) P hshift α] with ω hω
    funext t
    exact (hω t).symm
  have hCM : IndepFun (fun ω => (N ω).val) Y P :=
    indepFun_continuousMap_left_of_path_independence P (fun ω => (N ω).val) Y
      (hraw.congr heq Filter.EventuallyEq.rfl)
  have hclosed : IsClosed {f : C(ℝ,Configuration n) | f 0 = 0} :=
    isClosed_eq (continuous_eval_const 0) continuous_const
  have hec : Topology.IsClosedEmbedding (fun f : GinibreContinuousNoise n => f.val) :=
    hclosed.isClosedEmbedding_subtypeVal
  exact indepFun_of_measurable_embeddings P N Y (fun f => f.val) id
    hec.measurableEmbedding .id hCM

end
end GinibrePoincare
