module
public import GinibrePoincare.Endgame.FullTheoremOneNinePointwiseGamma

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The literal integrated pointwise curvature criterion (1.42), with ordinary
gradient energy represented by its actual weighted L² class. -/
theorem correspondence_integrated_pointwise_curvature {n : ℕ} (hn : 0<n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    2 * ginibreWeakEnergy n (ginibreFullCoreGradient hn f hf) ≤
      ∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n := by
  obtain ⟨g, hg, hfirst, hsecond⟩ := fullTheoremOneNinePointwiseGamma hn f hf
  have hgg : g = ginibreFullCoreGradient hn f hf :=
    ginibre_distributional_gradient_unique n hn _ _ _ hg
      (ginibreFullCorePair hn f hf).property.1
  subst g
  have htail := modeTail_nonneg
    (positiveHermiteModeMass hn
      (ginibreFullCenteredTransform n hn (ginibreFullCoreValue hn f hf)))
    (fun k => sq_nonneg _)
  nlinarith [sq_nonneg ‖ginibreFullCorePregenerator hn f hf + (2 : ℝ) •
    ginibreFullCenter n hn (ginibreFullCoreValue hn f hf)‖,
    sq_nonneg ‖ginibreFullHolomorphicRemainder n hn (ginibreFullCoreValue hn f hf)‖]

/-- The specific Ginibre Poincaré and integrated-curvature assertions are
equivalent. Both sides are established independently by concrete deficit
identities; this is not a universal external Bakry–Émery equivalence theorem. -/
theorem correspondence_poincare_iff_integrated_pointwise_curvature
    {n : ℕ} (hn : 0<n) :
    (∀ (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n),
      IsGinibreDistributionalGradient n u g → IsGinibreSymmetricWeakPair (u, g) →
      ginibreL2Variance n hn u ≤ ginibreWeakEnergy n g / 2) ↔
    (∀ (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f),
      2 * ginibreWeakEnergy n (ginibreFullCoreGradient hn f hf) ≤
        ∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n) := by
  constructor
  · intro _ f hf
    exact correspondence_integrated_pointwise_curvature hn f hf
  · intro _ u g hg hs
    exact ginibre_symmetric_weak_poincare hn u g hg hs

#print axioms correspondence_integrated_pointwise_curvature
#print axioms correspondence_poincare_iff_integrated_pointwise_curvature
end
end GinibrePoincare
