module

public import GinibrePoincare.Analysis.GaussianBlockRadialLaw
public import GinibrePoincare.Analysis.GinibreHamiltonianRadialGenerator
public import GinibrePoincare.Analysis.PairwiseRadius

@[expose] public section

open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- The literal squared norm of a standard complex Gaussian is Gamma(1,1). -/
theorem standardComplexGaussian_normSq_gamma :
    standardComplexGaussianMeasure.map Complex.normSq=gammaMeasure 1 1 := by
  have he : (gaussianBlockMeasure 1 1).map (fun z : Configuration 1 => z 0)=
      standardComplexGaussianMeasure := by
    exact (measurePreserving_eval (fun _ : Fin 1 =>
      (complexCoordinateGaussianProbability 1 : Measure ℂ)) 0).map_eq
  have hr : gaussianBlockRadius 1 1=(fun z : Configuration 1 => Complex.normSq (z 0)) := by
    funext z
    simp [gaussianBlockRadius,configurationNormSq]
  rw [← he,Measure.map_map Complex.continuous_normSq.measurable (measurable_pi_apply 0)]
  change (gaussianBlockMeasure 1 1).map (fun z : Configuration 1 => Complex.normSq (z 0))=gammaMeasure 1 1
  rw [← hr]
  simpa using gaussianBlockRadius_gamma 1 1 (by decide) (by decide)

/-- Exact equilibrium law of the center CIR observable. -/
theorem ginibreCenterSquared_equilibrium_gamma (n : ℕ) (hn : 0 < n) :
    (ginibreMeasure n).map (ginibreCenterSquared n)=gammaMeasure 1 1 := by
  rw [← standardComplexGaussian_normSq_gamma,← coordinateSum_ginibre_gaussian n hn,
    Measure.map_map Complex.continuous_normSq.measurable (measurable_coordinateSum n)]
  rfl

/-- The actual two equilibrium CIR radii are independent. -/
theorem ginibreCenterSquared_pairwiseRadius_independent (n : ℕ) (hn : 0 < n) :
    IndepFun (ginibreCenterSquared n) (pairwiseRadius : Configuration n → ℝ)
      (ginibreMeasure n) := by
  exact (coordinateSum_pairwiseRadius_indepFun n hn).comp
    Complex.continuous_normSq.measurable measurable_id

/-- Exact joint Gamma product law of both concrete equilibrium radii. -/
theorem ginibreTwoRadius_equilibrium_gamma_product (n : ℕ) (hn : 2 ≤ n) :
    (ginibreMeasure n).map (fun z => (ginibreCenterSquared n z,pairwiseRadius z))=
      (gammaMeasure 1 1).prod (gammaMeasure (recenteredGammaShape n : ℝ) 1) := by
  letI := ginibreMeasure_isProbabilityMeasure (by omega : 0<n)
  have hmS : Measurable (ginibreCenterSquared n) :=
    Complex.continuous_normSq.measurable.comp (measurable_coordinateSum n)
  have hmR : Measurable (pairwiseRadius : Configuration n → ℝ) := by
    unfold pairwiseRadius
    fun_prop
  rw [(ginibreCenterSquared_pairwiseRadius_independent n (by omega)).map_prod_eq_prod_map_map
    hmS.aemeasurable hmR.aemeasurable,ginibreCenterSquared_equilibrium_gamma n (by omega)]
  rw [recenteredGammaShape_eq n (by omega),pairwiseRadius_ginibre_gamma n hn]

#print axioms ginibreCenterSquared_pairwiseRadius_independent
#print axioms ginibreTwoRadius_equilibrium_gamma_product

#print axioms standardComplexGaussian_normSq_gamma
#print axioms ginibreCenterSquared_equilibrium_gamma
end
end GinibrePoincare
