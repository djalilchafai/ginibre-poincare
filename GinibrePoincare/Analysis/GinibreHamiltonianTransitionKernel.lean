module

public import GinibrePoincare.Analysis.GinibreHamiltonianBrownianRestart
public import Mathlib.Probability.Kernel.Composition.Prod

@[expose] public section

/-! Genuine Borel transition kernels obtained from the constructed canonical Brownian solution. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

def ginibreCanonicalTransitionKernel {n : ℕ} (hn : 0 < n) (α : ℝ) (t : ℝ≥0)
    (μ : Measure (GinibreContinuousNoise n)) :
    Kernel {z : Configuration n // CollisionFree z} (Configuration n) :=
  ((Kernel.id : Kernel {z : Configuration n // CollisionFree z} _) |>.prod
    (Kernel.const {z : Configuration n // CollisionFree z} μ)).map
    (fun p => ginibreDrivenMaximalValue n α p.2.val p.1.val t)

instance ginibreCanonicalTransitionKernel_isMarkov {n : ℕ} (hn : 0 < n)
    (α : ℝ) (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (ginibreCanonicalTransitionKernel hn α t μ) := by
  unfold ginibreCanonicalTransitionKernel
  exact Kernel.IsMarkovKernel.map _ (ginibreDrivenMaximalValue_joint_measurable hn α t)

def ginibreBrownianTransitionKernel {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (t : ℝ≥0) :
    Kernel {z : Configuration n // CollisionFree z} (Configuration n) :=
  ginibreCanonicalTransitionKernel hn α t (P.map (ginibreBrownianFullContinuousNoise n B α))

theorem ginibreBrownianTransitionKernel_isMarkov {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (t : ℝ≥0) :
    IsMarkovKernel (ginibreBrownianTransitionKernel hn α B P t) := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  letI : IsProbabilityMeasure (P.map (ginibreBrownianFullContinuousNoise n B α)) :=
    (by infer_instance)
  exact ginibreCanonicalTransitionKernel_isMarkov hn α t _

theorem ginibreCanonicalTransitionKernel_apply {n : ℕ} (hn : 0 < n) (α : ℝ)
    (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ]
    (z : {z : Configuration n // CollisionFree z}) :
    ginibreCanonicalTransitionKernel hn α t μ z =
      μ.map (fun N => ginibreDrivenMaximalValue n α N.val z.val t) := by
  unfold ginibreCanonicalTransitionKernel
  rw [Kernel.map_apply _ (ginibreDrivenMaximalValue_joint_measurable hn α t),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (ginibreDrivenMaximalValue_joint_measurable hn α t) measurable_prodMk_left]
  rfl


theorem ginibreBrownianTransitionKernel_apply_eq_process_law
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (t : ℝ≥0) (z : {z : Configuration n // CollisionFree z}) :
    ginibreBrownianTransitionKernel hn α B P t z =
      P.map (ginibreBrownianMaximalProcess n α z.val B t) := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  letI : IsProbabilityMeasure (P.map (ginibreBrownianFullContinuousNoise n B α)) :=
    (by infer_instance)
  unfold ginibreBrownianTransitionKernel
  rw [ginibreCanonicalTransitionKernel_apply,
    Measure.map_map (ginibreDrivenMaximalValue_measurable hn α z.val t) hm]
  rfl


end
end GinibrePoincare
