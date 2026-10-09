module

public import GinibrePoincare.Analysis.GinibreEqualityWeakDeficit
public import GinibrePoincare.Analysis.GinibreFullGeneratorVariational

@[expose] public section

/-! # Deficits from the variational generator graph

The graph characterization supplies a symmetric distributional gradient and
its variational pairing with every weak test pair. Test with the centered
value to identify Dirichlet energy with minus the generator pairing. The
weak-domain first deficit already supplies Hermite tail summability; expanding
the shifted generator norm and inserting the pairing gives the second deficit.
Neither weak differentiability nor summability is an input beyond graph membership.
-/

noncomputable section
namespace GinibrePoincare
open MeasureTheory
set_option maxHeartbeats 600000

/-- Both exact deficit identities hold on the actual full real generator graph.
The gradient and convergent spectral tail are consequences of graph membership. -/
theorem ginibreFullGenerator_deficit_identities {n : ℕ} (hn : 0 < n)
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
          8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
  obtain ⟨g, hug, hsg, hvar⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp hgraph
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u.val g hug hsg
  have he : ginibreWeakEnergy n g = -inner ℝ v.val (ginibreFullCenter n hn u.val) := by
    simpa only [ginibreWeakEnergy, real_inner_self_eq_norm_sq] using
      hvar (ginibreFullCenter n hn u.val) g huc hsc
  obtain ⟨ht, hfirst⟩ := ginibreFullWeak_first_deficit_identity hn u.val g hug hsg
  refine ⟨g, hug, hsg, ht, hfirst,?_⟩
  rw [norm_add_sq_real, real_inner_smul_right, norm_smul]
  norm_num
  rw [mul_pow, ginibreFullCenter_variance]
  nlinarith [he, hfirst]

end GinibrePoincare
