module

public import GinibrePoincare.Analysis.GinibreFullSemigroupRegularityDynamics
public import GinibrePoincare.Analysis.GinibreFullSemigroupMarkov

@[expose] public section

/-! # The genuine weak heat equation for all weighted L² initial data -/
open MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

/-- Every actual real L² datum evolves into an ordinary weak Sobolev function and
solves the original diffusion equation against every symmetric weak test,
classically in time, at every positive time. -/
theorem ginibreFullRealEvolution_weak_heat (n : ℕ) (hn : 0 < n)
    (x : ginibreFullSymmetricValues n) {t : ℝ} (ht : 0 < t) :
    ∃ (v : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n),
      HasDerivAt (fun s : ℝ => ginibreFullRealEvolution n hn (Real.toNNReal s) x) v t ∧
      IsGinibreDistributionalGradient n (ginibreFullRealEvolution n hn (Real.toNNReal t) x).val g ∧
      IsGinibreSymmetricWeakPair ((ginibreFullRealEvolution n hn (Real.toNNReal t) x).val, g) ∧
      ∀ w : GinibreFullValueL2 n, ∀ h : GinibreFullGradientL2 n,
        IsGinibreDistributionalGradient n w h → IsGinibreSymmetricWeakPair (w, h) →
        (1 / (n : ℝ)) * inner ℝ g h = -inner ℝ v.val w := by
  obtain ⟨V, hg, hd⟩ := ginibreFullEvolution_positive_time_dynamics n hn
    (ginibreFullSymmetricOfReal n x) ht
  let u := ginibreFullRealEvolution n hn (Real.toNNReal t) x
  let v := ginibreFullSymmetricRe n V
  have hr := ((ginibreFullGenerator_graph_iff_real_imag hn _ V).mp hg).1
  have hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
    apply (ginibreFullGenerator_graph_iff_real_imag hn _ _).mpr
    constructor
    · simpa only [ginibreFullSymmetricRe_ofReal, u, v, ginibreFullRealEvolution,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using hr
    · simp
  obtain ⟨g, hu, hs, he⟩ :=
    (ginibreFullGenerator_real_graph_iff_exists_gradient hn u v).mp hgraph
  refine ⟨v, g, ?_, hu, hs, he⟩
  exact (ginibreFullSymmetricRe n).hasFDerivAt.comp_hasDerivAt t hd

/-- Actual positive-time diffusion dissipates precisely its ordinary weak gradient
energy, for every real weighted L² initial datum. -/
theorem ginibreFullRealEvolution_energy_dissipation (n : ℕ) (hn : 0 < n)
    (x : ginibreFullSymmetricValues n) {t : ℝ} (ht : 0 < t) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n (ginibreFullRealEvolution n hn (Real.toNNReal t) x).val g ∧
      IsGinibreSymmetricWeakPair ((ginibreFullRealEvolution n hn (Real.toNNReal t) x).val, g) ∧
      HasDerivAt (fun s : ℝ => ‖ginibreFullRealEvolution n hn (Real.toNNReal s) x‖ ^ 2)
        (-2 * ginibreWeakEnergy n g) t := by
  obtain ⟨v, g, hd, hu, hs, he⟩ := ginibreFullRealEvolution_weak_heat n hn x ht
  refine ⟨g, hu, hs, ?_⟩
  have hform := he (ginibreFullRealEvolution n hn (Real.toNNReal t) x).val g hu hs
  have hnorm : inner ℝ g g = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  rw [hnorm] at hform
  have hi : inner ℝ (ginibreFullRealEvolution n hn (Real.toNNReal t) x) v =
      -ginibreWeakEnergy n g := by
    rw [real_inner_comm]
    change inner ℝ v.val (ginibreFullRealEvolution n hn (Real.toNNReal t) x).val = _
    unfold ginibreWeakEnergy
    linarith
  have hh := hd.norm_sq
  rw [hi] at hh
  simpa only [mul_neg, neg_mul] using hh

end
end GinibrePoincare
