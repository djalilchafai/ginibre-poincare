module

public import GinibrePoincare.Analysis.GinibreHamiltonianGradientPathWeight
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Borel measurability of the genuine Hamiltonian action on continuous paths. -/
open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

local instance GinibreHamiltonianGradientPathMeasure_instance1 (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance GinibreHamiltonianGradientPathMeasure_instance2 (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

theorem ginibreHamiltonian_action_measurable (n : ℕ) : Measurable (ginibreHamiltonian n) := by
  unfold ginibreHamiltonian
  exact (measurable_const.mul (contDiff_configurationNormSq (n := n)).continuous.measurable).sub
    (Real.measurable_log.comp (contDiff_vandermondeWeight n).continuous.measurable)

theorem ginibreHamiltonianGradientNormSq_measurable (n : ℕ) :
    Measurable (ginibreHamiltonianGradientNormSq n) := by
  unfold ginibreHamiltonianGradientNormSq
  apply Finset.measurable_sum
  intro j hj
  exact ((measurable_fderiv_apply_const ℝ (ginibreHamiltonian n)
    (realCoordinateDirection j)).pow_const 2).add
    ((measurable_fderiv_apply_const ℝ (ginibreHamiltonian n)
      (imaginaryCoordinateDirection j)).pow_const 2)

theorem ginibreHamiltonianPathEnergy_measurable (n : ℕ) (α T : ℝ) :
    Measurable (fun x : C(ℝ, Configuration n) => ginibreHamiltonianPathEnergy n α T x) := by
  have hm : Measurable (fun p : C(ℝ, Configuration n) × ℝ =>
      ginibreHamiltonianGradientNormSq n (p.1 p.2)) :=
    (ginibreHamiltonianGradientNormSq_measurable n).comp continuous_eval.measurable
  have hi (s : Set ℝ) : Measurable (fun x : C(ℝ, Configuration n) =>
      ∫ t in s, ginibreHamiltonianGradientNormSq n (x t)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  unfold ginibreHamiltonianPathEnergy intervalIntegral
  exact measurable_const.mul ((hi (Ioc 0 T)).sub (hi (Ioc T 0)))

theorem ginibreHamiltonianGradientPathWeight_measurable (n : ℕ) (α T : ℝ) :
    Measurable (fun x : C(ℝ, Configuration n) =>
      ginibreHamiltonianGradientPathWeight n α T x) := by
  unfold ginibreHamiltonianGradientPathWeight
  have h0 : Measurable (fun x : C(ℝ, Configuration n) => ginibreHamiltonian n (x 0)) := (ginibreHamiltonian_action_measurable n).comp (continuous_eval_const (0 : ℝ)).measurable
  have hT : Measurable (fun x : C(ℝ, Configuration n) => ginibreHamiltonian n (x T)) := (ginibreHamiltonian_action_measurable n).comp (continuous_eval_const T).measurable
  exact Real.measurable_exp.comp
    ((((h0.add hT).neg.div_const 2).add_const (2*α*T)).sub
      (ginibreHamiltonianPathEnergy_measurable n α T))

#print axioms ginibreHamiltonian_action_measurable
#print axioms ginibreHamiltonianGradientNormSq_measurable
#print axioms ginibreHamiltonianPathEnergy_measurable
#print axioms ginibreHamiltonianGradientPathWeight_measurable
end
end GinibrePoincare
