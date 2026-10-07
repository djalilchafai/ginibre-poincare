module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityCompactTests
public import GinibrePoincare.Analysis.GinibreInteriorWeakGradient
public import GinibrePoincare.Analysis.GaussianFourierCoordinates

@[expose] public section
open Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Every genuine compact collision-free domain admits a compact smooth cutoff
which is identically one on a neighborhood of that domain. -/
theorem ginibreLocalRegularity_exists_compact_interior_cutoff
    (n : ℕ) (hn : 0 < n) (K : Set (Configuration n)) (hK : IsCompact K)
    (hs : K ⊆ {z | CollisionFree z}) :
    ∃ η : Configuration n → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ {z | CollisionFree z} ∧ ∀ z ∈ K, η =ᶠ[𝓝 z] 1 := by
  let e := configurationEuclideanEquiv n
  obtain ⟨χ₀,hχ₀,hχ₀c,hχ₀one⟩ := ginibreLocalRegularity_exists_compact_cutoff (e '' K) (hK.image e.continuous)
  let χ := χ₀ ∘ e
  have hχ : ContDiff ℝ ∞ χ := hχ₀.comp e.contDiff
  have hχc : HasCompactSupport χ := hχ₀c.comp_homeomorph e.toHomeomorph
  have hχone (z) (hz : z ∈ K) : χ =ᶠ[𝓝 z] 1 :=
    (hχ₀one (e z) ⟨z,hz,rfl⟩).comp_tendsto e.continuous.continuousAt
  obtain ⟨ψ,hψ,hψs,hψone⟩ := exists_ginibreInteriorCutoff n hn K hK hs
  refine ⟨χ*ψ,hχ.mul hψ,hχc.mul_right,tsupport_mul_subset_right.trans hψs,?_⟩
  intro z hz
  filter_upwards [hχone z hz,hψone z hz] with x hx hy
  simp [hx,hy]

#print axioms ginibreLocalRegularity_exists_compact_interior_cutoff
end
end GinibrePoincare
