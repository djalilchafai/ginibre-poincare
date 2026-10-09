module

public import GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumInputs
public import GinibrePoincare.Analysis.GinibreHamiltonianJointEvaluation

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : MeasurableSpace C(ℝ, ℂ) := borel _
local instance : BorelSpace C(ℝ, ℂ) := ⟨rfl⟩

/-- Joint measurability in the initial center and its entire continuous noise. -/
theorem ginibreOU_initial_noise_joint_measurable (n : ℕ) (α : ℝ) (t : ℝ≥0) :
    Measurable (fun p : ℂ × C(ℝ, ℂ) => drivenOUPath (2*α/(n : ℝ)) p.1 p.2 t) := by
  have hj : Continuous (fun p : C(ℝ, ℂ) × ℝ => Real.exp ((2*α/(n : ℝ))*p.2) • p.1 p.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul continuous_eval
  have hInt : Measurable (fun N : C(ℝ, ℂ) => ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp ((2*α/(n : ℝ))*s) • N s) := by
    have hi := hj.measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.measurable
  exact ((continuous_eval_const (t : ℝ)).measurable.comp measurable_snd).add
    (measurable_const.smul (measurable_fst.sub (measurable_const.smul (hInt.comp measurable_snd))))

/-- Joint measurable whole OU solution path, with random initial center. -/
theorem ginibreOU_initial_noise_path_measurable (n : ℕ) (α : ℝ) :
    Measurable (fun p : ℂ × C(ℝ, ℂ) => fun t : ℝ≥0 =>
      drivenOUPath (2*α/(n : ℝ)) p.1 p.2 t) := by
  apply measurable_pi_lambda
  intro t
  exact ginibreOU_initial_noise_joint_measurable n α t

end
end GinibrePoincare
