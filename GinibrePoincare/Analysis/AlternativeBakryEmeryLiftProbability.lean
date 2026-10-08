module
public import GinibrePoincare.Analysis.BakryEmeryRegularizationVolume
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- Gaussian confinement makes the actual unregularized lift density integrable. -/
theorem bakryEmeryEuclideanLift_density_integrable
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    Integrable (fun x : E => Real.exp (-bakryEmeryEuclideanLiftPotential n V x)) volume := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hG : Integrable (fun x : E => Real.exp (-((n:ℝ)*ρ)/2*‖x‖^2)) volume := by
    simpa only [neg_div] using bakryEmery_gaussian_majorant_integrable (E := E)
      ((n:ℝ)*ρ/2) (by positivity)
  have hcont : Continuous (bakryEmeryEuclideanLiftPotential (E := E) n V) :=
    continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp continuous_norm))
  apply (hG.const_mul (Real.exp (-(n:ℝ)*V 0))).mono' hcont.neg.rexp.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro x
  have hd := bakryEmeryRegularizedLift_density_domination n ρ 0 hρ.le hrot hc x
  simpa [bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
    Real.sqrt_sq (norm_nonneg x), Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hd

/-- The literal unregularized Euclidean Gibbs lift is a probability law. -/
theorem bakryEmeryEuclideanLift_gibbs_probability
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    IsProbabilityMeasure (bakryEmeryNormalizedGibbs (volume : Measure E)
      (bakryEmeryEuclideanLiftPotential n V)) := by
  exact bakryEmeryNormalizedGibbs_probability volume _
    (continuous_const.mul (hV.comp (Complex.continuous_ofReal.comp continuous_norm)))
    (bakryEmeryEuclideanLift_density_integrable n hn ρ hρ V hV hrot hc)

/-- Absolute continuity for the actual lift, used to transfer Rademacher limits. -/
theorem bakryEmeryEuclideanLift_gibbs_absolutelyContinuous (n : ℕ) (V : Potential) :
    bakryEmeryNormalizedGibbs (volume : Measure E) (bakryEmeryEuclideanLiftPotential n V) ≪ volume := by
  exact (withDensity_absolutelyContinuous _ _).smul_left _

#print axioms bakryEmeryEuclideanLift_density_integrable
#print axioms bakryEmeryEuclideanLift_gibbs_probability
#print axioms bakryEmeryEuclideanLift_gibbs_absolutelyContinuous
end
end GinibrePoincare
