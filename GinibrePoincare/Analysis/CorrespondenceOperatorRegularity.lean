module
public import GinibrePoincare.Analysis.CorrespondenceOperatorSmoothIdentification
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityInteriorCutoff
public import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
public import Mathlib.Topology.UniformSpace.HeineCantor
@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Uniform density of the literal smooth compact collision-free core in the
continuous compact collision-free functions. Together with the proved form
closure, this is the two density conditions for regularity on collision-free
configuration space. -/
theorem correspondenceOperator_uniform_core_density (n : ℕ) (hn : 0<n)
    (f : Configuration n → ℝ) (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ {z | CollisionFree z}) (ε : ℝ) (hε : 0<ε) :
    ∃ g : Configuration n → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      tsupport g ⊆ {z | CollisionFree z} ∧ ∀ z, dist (g z) (f z)<ε := by
  obtain ⟨η, hη, hηc, hηs, hηone⟩ := ginibreLocalRegularity_exists_compact_interior_cutoff
    n hn (tsupport f) hc hs
  obtain ⟨C, hC⟩ := hηc.exists_bound_of_continuous hη.continuous
  let D := max C 1
  have hD : 0<D := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hηbound (z) : ‖η z‖≤D := (hC z).trans (le_max_left _ _)
  have huf : UniformContinuous f := hc.uniformContinuous_of_continuous hf
  obtain ⟨g, hg, hgf⟩ := huf.exists_contDiff_dist_le (div_pos hε hD)
  refine ⟨fun z => η z*g z, hη.mul hg, hηc.mul_right,
    tsupport_mul_subset_left.trans hηs,?_⟩
  intro z
  have hηf : η z*f z=f z := by
    by_cases hz : z∈tsupport f
    · have hh := (hηone z hz).self_of_nhds
      simpa only [Pi.one_apply, hh, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hz, mul_zero]
  have herr : η z*g z-f z=η z*(g z-f z) := by
    rw [mul_sub, hηf]
  rw [dist_eq_norm, herr, norm_mul]
  have hdist := hgf z
  rw [dist_eq_norm] at hdist
  calc
    ‖η z‖*‖g z-f z‖ ≤ D*‖g z-f z‖ :=
      mul_le_mul_of_nonneg_right (hηbound z) (norm_nonneg _)
    _ < D*(ε/D) := mul_lt_mul_of_pos_left hdist hD
    _ = ε := mul_div_cancel₀ _ hD.ne'

#print axioms correspondenceOperator_uniform_core_density
end
end GinibrePoincare
