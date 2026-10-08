module
public import GinibrePoincare.Analysis.CorrespondenceOperatorOUSmoothing
public import GinibrePoincare.Analysis.CollisionNull
public import GinibrePoincare.Analysis.GinibreMassFiniteness
public import Mathlib.Probability.Kernel.Composition.MeasureComp
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Ginibre and configuration Lebesgue measure have the same null sets. -/
theorem correspondenceOperator_volume_absolutelyContinuous_ginibre {n : ℕ} (hn : 0<n) :
    (volume:Measure (Configuration n)) ≪ ginibreMeasure n := by
  have hac : (volume:Measure (Configuration n)) ≪ complexGaussianMeasure n := by
    rw [complexGaussianDensityIdentification n hn]
    apply withDensity_absolutelyContinuous'
    · apply Measurable.aemeasurable
      unfold complexGaussianDensity gaussianWeight configurationNormSq
      fun_prop
    · exact ae_of_all _ (fun z => by
        unfold complexGaussianDensity gaussianWeight
        apply ne_of_gt
        apply ENNReal.ofReal_pos.mpr
        have hnR : 0<(n:ℝ) := by exact_mod_cast hn
        positivity)
  exact hac.trans (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure (ginibreMassEvaluation n hn))

/-- Every positive-time concrete Brownian transition has a density against the
actual invariant Ginibre measure. -/
theorem correspondenceOperator_transition_absolutelyContinuous_ginibre
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0<n)
    (α : ℝ≥0) (hα : 0<α) (B : (Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀i,IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) (ht : 0<t)
    (z : {z : Configuration n // CollisionFree z}) :
    ginibreBrownianTransitionKernel hn α B P t z ≪ ginibreMeasure n := by
  rw [ginibreBrownianTransitionKernel_apply_eq_process_law hn α B P hB t z]
  exact (correspondenceOperator_original_endpoint_absolutelyContinuous_volume hn α hα B P hB hind
    z.val z.property t ht).trans (correspondenceOperator_volume_absolutelyContinuous_ginibre hn)

/-- Invariance at a single strictly positive time already forces every arbitrary
initial invariant measure to possess a Ginibre density. No L² density hypothesis
or permutation symmetry is imposed. -/
theorem correspondenceOperator_invariant_absolutelyContinuous_ginibre
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0<n)
    (α : ℝ≥0) (hα : 0<α) (B : (Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀i,IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) (ht : 0<t)
    (ν : Measure {z : Configuration n // CollisionFree z})
    (hInv : ginibreBrownianTransitionKernel hn α B P t ∘ₘ ν=ν.map Subtype.val) :
    ν.map Subtype.val ≪ ginibreMeasure n := by
  rw [← hInv]
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  have he : (fun z => ginibreBrownianTransitionKernel hn α B P t z s)=fun _ => 0 := by
    funext z
    exact (correspondenceOperator_transition_absolutelyContinuous_ginibre hn α hα B P hB hind t ht z) hs0
  rw [he,lintegral_zero]
#print axioms correspondenceOperator_volume_absolutelyContinuous_ginibre
#print axioms correspondenceOperator_transition_absolutelyContinuous_ginibre
#print axioms correspondenceOperator_invariant_absolutelyContinuous_ginibre
end
end GinibrePoincare
