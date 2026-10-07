module

public import GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import GinibrePoincare.Analysis.GinibreFullSemigroupPaperSpeed
public import GinibrePoincare.Analysis.GinibreStochasticGeneratorNormalization

@[expose] public section

/-! The actual analytic evolution and original Brownian drift have the same
paper-normalized generator on the concrete collision-free symmetric core.
This module does not assert equality of the transition operators. -/
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Actual analytic evolution has the paper-speed derivative on every concrete
smooth symmetric collision-free compact test function. -/
theorem ginibreTransitionAnalyticCore_right_derivative {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    HasDerivWithinAt
      (fun t : ℝ => ginibreFullPaperEvolution n hn α (Real.toNNReal t)
        (ginibreFullSymmetricOfReal n (ginibreFullCoreSymmetricValue hn f hf)))
      (((α : ℝ) / (n : ℝ)) •
        ginibreFullSymmetricOfReal n (ginibreFullCoreSymmetricPregenerator hn f hf))
      (Set.Ici 0) 0 :=
  ginibreFullPaperEvolution_right_derivative n hn α _ _
    (ginibreFullGenerator_core_graph hn f hf)

/-- The original Brownian drift and quadratic-variation correction on the same
test core are precisely the pointwise paper-speed differential generator. -/
theorem ginibreTransitionAnalyticCore_ito_generator {n : ℕ} (hn : 0 < n)
    (α : ℝ≥0) (f : Configuration n → ℝ) (_hf : IsTheoremOneNineCore f)
    (z : Configuration n) (hz : CollisionFree z) :
    fderiv ℝ f z (ginibreLangevinDrift n (α : ℝ) z) +
      ((α : ℝ) / (n : ℝ)^2) * configurationLaplacian f z =
      ginibreRealPaperSpeedGenerator n (α : ℝ) f z :=
  ginibreLangevin_fderiv_generator hn (α : ℝ) f z hz

#print axioms ginibreTransitionAnalyticCore_right_derivative
#print axioms ginibreTransitionAnalyticCore_ito_generator
end
end GinibrePoincare
