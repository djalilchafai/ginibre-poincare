module

public import GinibrePoincare.Analysis.GinibreEqualityWeakAffine
public import GinibrePoincare.Analysis.GinibreFullSemigroupDeficitConsequences

@[expose] public section

/-! # Theorem 1.9 on the actual full generator domain

Both sum-of-squares identities hold for every real symmetric generator-domain
observable. Its weak gradient and the convergent Hermite tail follow from graph
membership. Equality in the sharp Poincaré inequality is classified on the
entire weak domain, including non-polynomial observables and L² limits.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Full concrete Theorem 1.9, with exact deficit identities and exhaustive
weak affine equality classification. -/
theorem fullTheoremOneNine {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      Summable (fun k : ℕ => (k : ℝ) *
        positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) ∧
      (ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
        ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => a + 2 * (c * coordinateSum z).re) := by
  obtain ⟨g, hu, hs, ht, hfirst, hsecond⟩ :=
    ginibreFullGenerator_deficit_identities hn u v hgraph
  exact ⟨g, hu, hs, ht, hfirst, hsecond,
    ginibreEquality_full_weak_affine_iff hn u.val g hu hs⟩

end
end GinibrePoincare
