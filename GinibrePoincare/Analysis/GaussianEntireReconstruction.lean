module

public import GinibrePoincare.Analysis.GaussianEntireRepresentatives
public import GinibrePoincare.Analysis.GaussianEntireDifferentiability
public import GinibrePoincare.Analysis.GaussianEntireHilbertIdentification

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Every holomorphic Hermite zero mode has an actual multivariate entire
representative, with no regularity hypothesis on the input class. -/
theorem gaussianZeroMode_has_entire_representative {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    gaussianHermiteMode hn 0 u ∈ gaussianEntireL2 n := by
  refine ⟨fun z => ∑' p, gaussianHermiteCoefficient hn u (p, 0) *
    ComplexHermite.multivariateNormalized n hn p 0 z, ?_, ?_⟩
  · exact differentiable_holomorphicHermite_series n hn _
      (fun p => gaussianHermiteCoefficient_norm_le hn u (p, 0))
  · exact gaussianZeroMode_holomorphic_series_ae hn u

#print axioms gaussianZeroMode_has_entire_representative

end
end GinibrePoincare
