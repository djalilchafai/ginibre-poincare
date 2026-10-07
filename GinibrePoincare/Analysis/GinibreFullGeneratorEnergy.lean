module

public import GinibrePoincare.Analysis.GinibreFullGeneratorVariational

@[expose] public section

noncomputable section
namespace GinibrePoincare
set_option backward.isDefEq.respectTransparency false

/-- Every actual full complex graph element has real and imaginary ordinary
weak gradients, and its quadratic form is their exact summed energy. -/
theorem ginibreFullGenerator_complex_energy_identity {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    ∃ gr gi : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n (ginibreFullSymmetricRe n u).val gr ∧
      IsGinibreSymmetricWeakPair ((ginibreFullSymmetricRe n u).val, gr) ∧
      IsGinibreDistributionalGradient n (ginibreFullSymmetricIm n u).val gi ∧
      IsGinibreSymmetricWeakPair ((ginibreFullSymmetricIm n u).val, gi) ∧
      ginibreWeakEnergy n gr + ginibreWeakEnergy n gi = -(inner ℂ v u).re := by
  obtain ⟨hr, hi⟩ := (ginibreFullGenerator_graph_iff_real_imag hn u v).mp hgraph
  have hrg : (ginibreFullSymmetricOfReal n (ginibreFullSymmetricRe n u),
      ginibreFullSymmetricOfReal n (ginibreFullSymmetricRe n v)) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal, hr]
  have hig : (ginibreFullSymmetricOfReal n (ginibreFullSymmetricIm n u),
      ginibreFullSymmetricOfReal n (ginibreFullSymmetricIm n v)) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff, ← map_sub, ginibreFullComplexResolvent_ofReal, hi]
  obtain ⟨gr, hgr, hsr, her⟩ := ginibreFullGenerator_real_energy_identity hn _ _ hrg
  obtain ⟨gi, hgi, hsi, hei⟩ := ginibreFullGenerator_real_energy_identity hn _ _ hig
  refine ⟨gr, gi, hgr, hsr, hgi, hsi, ?_⟩
  have hinner := ginibreFullComplex_inner_re n v.val u.val
  rw [her, hei]
  change -(inner ℝ (ginibreFullComplexRe n v.val) (ginibreFullComplexRe n u.val)) +
    -(inner ℝ (ginibreFullComplexIm n v.val) (ginibreFullComplexIm n u.val)) =
      -(inner ℂ v.val u.val).re
  rw [hinner]
  ring

/-- Dissipativity on the entire actual symmetric generator domain. -/
theorem ginibreFullGenerator_complex_dissipative {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    (inner ℂ v u).re ≤ 0 := by
  obtain ⟨gr, gi, _, _, _, _, he⟩ := ginibreFullGenerator_complex_energy_identity hn u v hgraph
  have hr : 0 ≤ ginibreWeakEnergy n gr := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  have hi : 0 ≤ ginibreWeakEnergy n gi := by
    exact mul_nonneg (by positivity) (sq_nonneg _)
  linarith

/-- The full complex generator quadratic form dominates twice the sum of the
real and imaginary centered variances throughout its exact graph domain. -/
theorem ginibreFullGenerator_complex_poincare {n : ℕ} (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hgraph : (u, v) ∈ (ginibreFullGenerator n hn).graph) :
    2 * (ginibreL2Variance n hn (ginibreFullSymmetricRe n u).val +
      ginibreL2Variance n hn (ginibreFullSymmetricIm n u).val) ≤ -(inner ℂ v u).re := by
  obtain ⟨gr, gi, hgr, hsr, hgi, hsi, he⟩ :=
    ginibreFullGenerator_complex_energy_identity hn u v hgraph
  have hr := ginibre_symmetric_weak_poincare hn _ gr hgr hsr
  have hi := ginibre_symmetric_weak_poincare hn _ gi hgi hsi
  linarith

end GinibrePoincare
