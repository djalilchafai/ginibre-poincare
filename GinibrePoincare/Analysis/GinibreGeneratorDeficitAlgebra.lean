module

public import GinibrePoincare.Analysis.GinibreFullGeneratorVariational
public import GinibrePoincare.Analysis.GinibreEqualityWeakVariational
public import GinibrePoincare.Analysis.GinibreFullGeneratorHermiteLowering

@[expose] public section

/-! # Generator deficit algebra independent of the Hermite deficit

The Γ₂ deficit reduces to twice the Poincaré deficit plus the squared shifted
generator. This identity uses only the actual weak generator pairing.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The generator identity used in the second part of Section 6, before choosing
any proof of the first deficit. The gradient is obtained from actual graph membership. -/
theorem ginibreGenerator_second_deficit_algebra {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      ‖v.val‖^2 - 2*ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖^2 +
          2*(ginibreWeakEnergy n g - 2*ginibreL2Variance n hn u.val) := by
  obtain ⟨g, hu, hs, hpair⟩ := (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp hgraph
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u.val g hu hs
  have he : ginibreWeakEnergy n g = -inner ℝ v.val (ginibreFullCenter n hn u.val) := by
    simpa only [ginibreWeakEnergy, real_inner_self_eq_norm_sq] using
      hpair (ginibreFullCenter n hn u.val) g huc hsc
  refine ⟨g, hu, hs,?_⟩
  rw [norm_add_sq_real, norm_smul, real_inner_smul_right]
  norm_num
  rw [mul_pow, ginibreFullCenter_variance]
  nlinarith [he]

#print axioms ginibreGenerator_second_deficit_algebra
end
end GinibrePoincare
