module

public import GinibrePoincare.Analysis.BakryEmeryRegularizationVolume

@[expose] public section

/-! The actual smooth radial Gibbs laws have finite positive mass in every
finite-dimensional real Hilbert space. Gaussian integrability is discharged
here rather than supplied as an analytic certificate. -/

open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem bakryEmeryRegularizedLift_density_integrable
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) (ε : ℝ) :
    Integrable (fun x : E => Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x)) volume := by
  have hG := bakryEmery_gaussian_majorant_integrable (E := E) ((n : ℝ)*ρ/2)
    (by positivity)
  have hm : Continuous (fun x : E => Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x)) :=
    Real.continuous_exp.comp ((continuous_const.mul (hV.comp
      (Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp
        ((continuous_norm.pow 2).add continuous_const))))).neg)
  apply (hG.const_mul (Real.exp (-(n : ℝ)*V 0))).mono hm.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  simpa only [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
    neg_div]
    using bakryEmeryRegularizedLift_density_domination n ρ ε hρ.le hrot hc x

theorem bakryEmeryRegularizedLift_gibbs_probability
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) (ε : ℝ) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs (volume : Measure E)
      (bakryEmeryRegularizedLiftPotential n V ε)) := by
  apply bakryEmeryNormalizedGibbs_probability
  · exact continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp
      (Real.continuous_sqrt.comp ((continuous_norm.pow 2).add continuous_const))))
  · exact bakryEmeryRegularizedLift_density_integrable n hn ρ hρ V hV hrot hc ε

#print axioms bakryEmeryRegularizedLift_density_integrable
#print axioms bakryEmeryRegularizedLift_gibbs_probability

end
end GinibrePoincare
