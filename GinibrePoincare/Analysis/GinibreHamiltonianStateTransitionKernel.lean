module

public import GinibrePoincare.Analysis.GinibreHamiltonianTransitionKernel

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreDrivenMaximalValue_collisionFree {n : ℕ} (α : ℝ)
    (N : GinibreContinuousNoise n) (z : {z : Configuration n // CollisionFree z}) (t : ℝ≥0) :
    CollisionFree (ginibreDrivenMaximalValue n α N.val z.val t) := by
  by_cases ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N.val z.val
  · have hd : (t : ℝ) ∈ ginibreDrivenMaximalDomain n α N.val z.val :=
      ⟨t.property,by simpa using ht⟩
    simpa only [ginibreDrivenMaximalPath,Real.toNNReal_coe] using
      (ginibreDrivenMaximalPath_equation hd).1
  · rw [show ginibreDrivenMaximalValue n α N.val z.val t=z.val from dif_neg ht]
    exact z.property

def ginibreCanonicalStateValue {n : ℕ} (α : ℝ) (t : ℝ≥0)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :
    {z : Configuration n // CollisionFree z} :=
  ⟨ginibreDrivenMaximalValue n α p.2.val p.1.val t,
    ginibreDrivenMaximalValue_collisionFree α p.2 p.1 t⟩

theorem ginibreCanonicalStateValue_measurable {n : ℕ} (hn : 0 < n) (α : ℝ) (t : ℝ≥0) :
    Measurable (ginibreCanonicalStateValue (n := n) α t) :=
  (ginibreDrivenMaximalValue_joint_measurable hn α t).subtype_mk

def ginibreCanonicalStateTransitionKernel {n : ℕ} (α : ℝ) (t : ℝ≥0)
    (μ : Measure (GinibreContinuousNoise n)) :
    Kernel {z : Configuration n // CollisionFree z} {z : Configuration n // CollisionFree z} :=
  ((Kernel.id : Kernel {z : Configuration n // CollisionFree z} _) |>.prod
    (Kernel.const {z : Configuration n // CollisionFree z} μ)).map (ginibreCanonicalStateValue α t)

theorem ginibreCanonicalStateTransitionKernel_isMarkov {n : ℕ} (hn : 0 < n)
    (α : ℝ) (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ] :
    IsMarkovKernel (ginibreCanonicalStateTransitionKernel (n := n) α t μ) := by
  unfold ginibreCanonicalStateTransitionKernel
  exact Kernel.IsMarkovKernel.map _ (ginibreCanonicalStateValue_measurable hn α t)

theorem ginibreCanonicalStateTransitionKernel_apply {n : ℕ} (hn : 0 < n) (α : ℝ)
    (t : ℝ≥0) (μ : Measure (GinibreContinuousNoise n)) [IsProbabilityMeasure μ]
    (z : {z : Configuration n // CollisionFree z}) :
    ginibreCanonicalStateTransitionKernel α t μ z =
      μ.map (fun N => ginibreCanonicalStateValue α t (z,N)) := by
  unfold ginibreCanonicalStateTransitionKernel
  rw [Kernel.map_apply _ (ginibreCanonicalStateValue_measurable hn α t),
    Kernel.prod_apply,Kernel.id_apply,Kernel.const_apply,Measure.dirac_prod,
    Measure.map_map (ginibreCanonicalStateValue_measurable hn α t) measurable_prodMk_left]
  rfl


end
end GinibrePoincare
