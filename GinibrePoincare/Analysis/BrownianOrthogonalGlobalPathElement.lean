module

public import GinibrePoincare.Analysis.BrownianOrthogonalJointOUFunctional

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The genuine joint event that a canonical driven solution is global. -/
theorem ginibreDriven_global_joint_measurableSet {n : ℕ} (hn : 0 < n) (α : ℝ) :
    MeasurableSet {p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n |
      ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤} := by
  have he : {p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n |
      ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤} =
      ⋂ k : ℕ, {p | ((k:ℝ≥0):ℝ≥0∞) < ginibreDrivenMaximalLifetime n α p.2.val p.1.val} := by
    ext p
    simp only [mem_setOf_eq,mem_iInter]
    constructor
    · intro h k
      rw [h]
      exact ENNReal.coe_lt_top
    · intro h
      apply top_unique
      rw [← ENNReal.iSup_natCast]
      apply iSup_le
      intro k
      exact (h k).le
  rw [he]
  exact MeasurableSet.iInter fun k => (ginibreDrivenMaximalLifetime_joint_alive_isOpen hn α k).measurableSet

/-- Canonical global paths bundled in the actual continuous-path space;
 nonglobal inputs use the constant initial path. -/
def ginibreDrivenGlobalPathElement {n : ℕ} (α : ℝ)
    (p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n) :
    C(ℝ,Configuration n) := by
  classical
  exact if h : ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤ then
    ⟨fun t => ginibreDrivenMaximalValue n α p.2.val p.1.val (Real.toNNReal t),
      (continuous_iff_continuousAt.mpr fun t =>
        ginibreDrivenMaximalValue_continuousAt_time t (by rw [h]; exact ENNReal.coe_lt_top)).comp
          continuous_real_toNNReal⟩
    else ContinuousMap.const ℝ p.1.val

/-- Genuine joint Borel measurability of the actual global canonical path element. -/
theorem ginibreDrivenGlobalPathElement_measurable {n : ℕ} (hn : 0 < n) (α : ℝ) :
    @Measurable _ C(ℝ,Configuration n) _ (borel _) (ginibreDrivenGlobalPathElement α) := by
  classical
  letI : MeasurableSpace C(ℝ,Configuration n) := borel _
  letI : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  have hm : Measurable (fun p : {z : Configuration n // CollisionFree z} × GinibreContinuousNoise n =>
      if ginibreDrivenMaximalLifetime n α p.2.val p.1.val = ⊤ then
        ginibreDrivenMaximalValue n α p.2.val p.1.val (Real.toNNReal t) else p.1.val) :=
    (ginibreDrivenMaximalValue_joint_measurable hn α (Real.toNNReal t)).ite
    (ginibreDriven_global_joint_measurableSet hn α)
    (continuous_subtype_val.comp continuous_fst).measurable
  convert hm using 1
  funext p
  simp only [ginibreDrivenGlobalPathElement]
  split <;> rfl

end
end GinibrePoincare
