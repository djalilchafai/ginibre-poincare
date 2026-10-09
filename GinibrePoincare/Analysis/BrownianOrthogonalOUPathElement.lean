module

public import GinibrePoincare.Analysis.BrownianOrthogonalJointOUFunctional

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section
local instance : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

def ginibreOUPathElement (n : ℕ) (α : ℝ) (p : ℂ × C(ℝ, ℂ)) : C(ℝ, ℂ) :=
  ⟨fun t => drivenOUPath (2*α/(n : ℝ)) p.1 p.2 (Real.toNNReal t),
    (drivenOUPath_continuous _ _ _ p.2.continuous).comp
      (NNReal.continuous_coe.comp continuous_real_toNNReal)⟩

theorem ginibreOUPathElement_measurable (n : ℕ) (α : ℝ) :
    Measurable (ginibreOUPathElement n α) := by
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  exact ginibreOU_initial_noise_joint_measurable n α (Real.toNNReal t)

end
end GinibrePoincare
