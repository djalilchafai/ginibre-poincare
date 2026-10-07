module

public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Topology.Compactness.LocallyFinite

@[expose] public section

/-! # Finite localization of actual compact smooth tests

A smooth partition of unity decomposes a compact smooth test into finitely many
compact smooth tests subordinate to an arbitrary open cover of its support.
-/

open scoped Topology ContDiff Manifold BigOperators
namespace GinibrePoincare
noncomputable section

/-- Finite decomposition of a compact smooth test along an open cover. -/
theorem exists_finite_smooth_test_decomposition
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {ι : Type*}
    (θ : E → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (U : ι → Set E) (hU : ∀ i, IsOpen (U i)) (hs : tsupport θ ⊆ ⋃ i, U i) :
    ∃ (I : Finset ι) (ψ : ι → E → ℝ),
      (∀ i, ContDiff ℝ ∞ (ψ i) ∧ HasCompactSupport (ψ i) ∧ tsupport (ψ i) ⊆ U i) ∧
      θ = fun x => ∑ i ∈ I, ψ i x := by
  classical
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    𝓘(ℝ, E) hc.isClosed U hU hs
  let I := (ρ.locallyFinite.finite_nonempty_inter_compact hc).toFinset
  let ψ : ι → E → ℝ := fun i x => ρ i x * θ x
  refine ⟨I, ψ, ?_, ?_⟩
  · intro i
    refine ⟨((contMDiff_iff_contDiff).mp (ρ i).contMDiff).mul hθ, ?_, ?_⟩
    · exact hc.mul_left
    · exact tsupport_mul_subset_left.trans (hρ i)
  · funext x
    by_cases hx : x ∈ tsupport θ
    · have hI : ρ.finsupport x ⊆ I := by
        intro i hi
        apply (Set.Finite.mem_toFinset _).mpr
        exact ⟨x, (ρ.mem_finsupport x).mp hi, hx⟩
      have he := ρ.sum_finsupport' x hx hI
      dsimp [ψ]
      rw [← Finset.sum_mul, he, one_mul]
    · have he := image_eq_zero_of_notMem_tsupport hx
      simp [ψ, he]

/-- A smooth cutoff supported in an open set and equal to one near a closed
subset. The support inclusion follows from a closed intermediate neighbourhood. -/
theorem exists_smooth_open_cutoff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (K U : Set E) (hK : IsClosed K)
    (hU : IsOpen U) (hs : K ⊆ U) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ tsupport χ ⊆ U ∧
      ∀ z ∈ K, χ =ᶠ[𝓝 z] 1 := by
  obtain ⟨G, hG, hKG, hGU⟩ := normal_exists_closure_subset hK hU hs
  have hKi : K ⊆ interior (closure G) :=
    hKG.trans (hG.subset_interior_iff.mpr subset_closure)
  obtain ⟨χ, hχ, hzχ, _⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    𝓘(ℝ, E) hK hKi (n := ⊤)
  refine ⟨χ, contMDiff_iff_contDiff.mp χ.contMDiff, ?_, ?_⟩
  · apply (closure_minimal ?_ isClosed_closure).trans hGU
    intro z hz
    by_contra hnot
    exact hz (hzχ z hnot)
  · intro z hz
    exact hχ.filter_mono (nhds_le_nhdsSet hz)

end
end GinibrePoincare
