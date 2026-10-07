module

public import GinibrePoincare.Analysis.NonQuadraticL2TensorOperators
public import Mathlib.Topology.MetricSpace.UniformConvergence

@[expose] public section

/-! # Strong limits on the genuine whole product L² space -/
open MeasureTheory Filter
open scoped Topology TensorProduct NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Uniformly bounded operators converge on a closed set of vectors. -/
theorem boundedOperators_isClosed_strong_limit
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    {ι : Type*} (l : Filter ι) (T : ι → H →L[ℂ] H) (C : ℝ≥0)
    (hb : ∀ i, ‖T i‖₊ ≤ C) :
    IsClosed {x : H | Tendsto (fun i => T i x) l (𝓝 x)} := by
  exact (LipschitzWith.uniformEquicontinuous (fun i x => T i x) C
    (fun i => (T i).lipschitz.weaken (hb i))).equicontinuous.isClosed_setOfPred_tendsto continuous_id

/-- Uniformly bounded actual product-L² operators which converge on pure
tensors converge strongly on every vector of the whole σ-finite product law. -/
theorem productL2_strong_limit_of_pure
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
    {ι : Type*} (l : Filter ι)
    (T : ι → Lp ℂ 2 (μ.prod ν) →L[ℂ] Lp ℂ 2 (μ.prod ν)) (C : ℝ≥0)
    (hb : ∀ i, ‖T i‖₊ ≤ C)
    (hp : ∀ u : Lp ℂ 2 μ, ∀ v : Lp ℂ 2 ν,
      Tendsto (fun i => T i (l2ProductVector u v)) l (𝓝 (l2ProductVector u v)))
    (F : Lp ℂ 2 (μ.prod ν)) : Tendsto (fun i => T i F) l (𝓝 F) := by
  obtain ⟨x, rfl⟩ := l2ProductCompletedTensorEquiv_sigmaFinite.surjective F
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    exact (boundedOperators_isClosed_strong_limit l T C hb).preimage
      (l2ProductCompletedTensorEquiv_sigmaFinite (μ := μ) (ν := ν)).continuous
  | ih x =>
    rw [l2ProductTensorEquiv_coe]
    induction x using TensorProduct.induction_on with
    | zero => simpa only [map_zero] using (tendsto_const_nhds : Tendsto (fun _ : ι => (0 : Lp ℂ 2 (μ.prod ν))) l (𝓝 0))
    | tmul u v => simpa only [l2ProductTensorMap_tmul] using hp u v
    | add x y hx hy => simpa only [map_add] using hx.add hy

/-- Scalar strong approximation transfers to the actual whole left
coordinate of a σ-finite product law, with the same uniform norm bound. -/
theorem productL2_left_strong_limit
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
    {ι : Type*} (l : Filter ι) (A : ι → Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (C : ℝ≥0) (hb : ∀ i, ‖A i‖₊ ≤ C)
    (ha : ∀ u, Tendsto (fun i => A i u) l (𝓝 u))
    (F : Lp ℂ 2 (μ.prod ν)) :
    Tendsto (fun i => l2ProductLeftOperator (ν := ν) (A i) F) l (𝓝 F) := by
  apply productL2_strong_limit_of_pure (μ := μ) (ν := ν) l
    (fun i => l2ProductLeftOperator (ν := ν) (A i)) C _ _ F
  · intro i
    exact_mod_cast (l2ProductLeftOperator_norm_le (ν := ν) (A i)).trans (show ‖A i‖ ≤ (C : ℝ) from hb i)
  · intro u v
    have he : (fun i => l2ProductLeftOperator (ν := ν) (A i) (l2ProductVector u v)) =
        (fun i => l2ProductVector (A i u) v) := funext (fun i => l2ProductLeftOperator_pure (A i) u v)
    rw [he]
    exact ((l2ProductContinuousBilinear (μ := μ) (ν := ν)).flip v).continuous.tendsto u |>.comp (ha u)

/-- Scalar strong approximation transfers to the actual whole right
coordinate of a σ-finite product law. -/
theorem productL2_right_strong_limit
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]
    {ι : Type*} (l : Filter ι) (A : ι → Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)
    (C : ℝ≥0) (hb : ∀ i, ‖A i‖₊ ≤ C)
    (ha : ∀ u, Tendsto (fun i => A i u) l (𝓝 u))
    (F : Lp ℂ 2 (μ.prod ν)) :
    Tendsto (fun i => l2ProductRightOperator (μ := μ) (A i) F) l (𝓝 F) := by
  apply productL2_strong_limit_of_pure (μ := μ) (ν := ν) l
    (fun i => l2ProductRightOperator (μ := μ) (A i)) C _ _ F
  · intro i
    exact_mod_cast (l2ProductRightOperator_norm_le (μ := μ) (A i)).trans (show ‖A i‖ ≤ (C : ℝ) from hb i)
  · intro u v
    have he : (fun i => l2ProductRightOperator (μ := μ) (A i) (l2ProductVector u v)) =
        (fun i => l2ProductVector u (A i v)) := funext (fun i => l2ProductRightOperator_pure (A i) u v)
    rw [he]
    exact (l2ProductContinuousBilinear (μ := μ) (ν := ν) u).continuous.tendsto v |>.comp (ha v)

end
end GinibrePoincare
