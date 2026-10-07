module

public import GinibrePoincare.Analysis.GinibreDrivenPathClippedLocalFlow
public import GinibrePoincare.Analysis.GinibreHamiltonianOUCompactLocalFlow

@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonianOU_compact_clipped_measurable_local_flow (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) :
    ∃ δ : ℝ, ∃ hδ : δ > 0, ∃ τ : ℝ, ∃ hτ : τ > 0,
    ∃ K : Set (Configuration n), IsCompact K ∧ (∀ x ∈ K, CollisionFree x) ∧
    ∃ Φ : C(Icc (-1 : ℝ) 1,Configuration n) → C(Icc 0 τ,Configuration n),
      @Measurable _ _ (borel C(Icc (-1 : ℝ) 1,Configuration n))
        (borel C(Icc 0 τ,Configuration n)) Φ ∧
      (∀ N, Φ N ⟨0,⟨le_rfl,hτ.le⟩⟩ = z) ∧
      (∀ N (t : Icc 0 τ), Φ N t ∈ K) ∧
      (∀ N (t : Icc 0 τ), Φ N t = z+
        drivenBoundedNoiseExtension (Configuration n) (drivenNoiseClipSmall δ hδ N).val t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • (Φ N (Set.projIcc 0 τ hτ.le s))) ∧
      ∀ N Q (t : Icc 0 τ),
        (∀ s ∈ Icc 0 (t : ℝ), N (Set.projIcc (-1 : ℝ) 1 (by norm_num) s) =
          Q (Set.projIcc (-1 : ℝ) 1 (by norm_num) s)) → Φ N t = Φ Q t := by
  obtain ⟨δ,hδ,τ,hτ,K,hK,hKCF,Ψ,hMeas,hZero,hCF,hEq,hCausal⟩ := ginibreHamiltonianOU_compact_measurable_local_flow n α z hz
  let Φ := fun N => Ψ (drivenNoiseClipSmall δ hδ N)
  have hΦ : @Measurable _ _ (borel C(Icc (-1 : ℝ) 1,Configuration n))
      (borel C(Icc 0 τ,Configuration n)) Φ :=
    hMeas.comp (drivenNoiseClipSmall_continuous δ hδ).borel_measurable
  refine ⟨δ,hδ,τ,hτ,K,hK,hKCF,Φ,hΦ,fun N => hZero _,fun N t => hCF _ t,fun N t => hEq _ t,?_⟩
  intro N Q t hPast
  apply hCausal
  intro s hs
  have h0 := hPast 0 ⟨le_rfl,t.property.1⟩
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)] at h0
  change drivenNoiseClip (drivenNoiseClipRadius δ) (N _-N _) = drivenNoiseClip (drivenNoiseClipRadius δ) (Q _-Q _)
  rw [hPast s hs,h0]

end
end GinibrePoincare

#print axioms GinibrePoincare.ginibreHamiltonianOU_compact_clipped_measurable_local_flow
