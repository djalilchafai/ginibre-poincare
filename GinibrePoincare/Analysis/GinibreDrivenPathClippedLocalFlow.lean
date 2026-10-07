module

public import GinibrePoincare.Analysis.GinibreDrivenPathNoiseClip

@[expose] public section

/-! Causal bounded-noise localization of the actual singular local flow. -/
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def drivenNoiseClipRadius (δ : ℝ) : ℝ := min 1 δ/2

theorem drivenNoiseClipRadius_pos (δ : ℝ) (hδ : 0 < δ) : 0 < drivenNoiseClipRadius δ := by
  dsimp [drivenNoiseClipRadius]
  positivity

theorem drivenNoiseClipRadius_lt (δ : ℝ) (hδ : 0 < δ) : drivenNoiseClipRadius δ < δ := by
  have := min_le_right (1 : ℝ) δ
  dsimp [drivenNoiseClipRadius]
  linarith

theorem drivenNoiseClipRadius_le_one (δ : ℝ) : drivenNoiseClipRadius δ ≤ 1 := by
  have := min_le_left (1 : ℝ) δ
  dsimp [drivenNoiseClipRadius]
  linarith

def drivenNoiseClipSmall (δ : ℝ) (hδ : 0 < δ) (N : C(Icc (-1 : ℝ) 1,E)) : drivenSmallNoiseSpace E δ :=
  ⟨⟨drivenNoiseClipPath (drivenNoiseClipRadius δ) (drivenNoiseClipRadius_pos δ hδ) N,
      drivenNoiseClipPath_zero _ _ N, fun t =>
        (drivenNoiseClip_norm_le _ (drivenNoiseClipRadius_pos δ hδ) _).trans (drivenNoiseClipRadius_le_one δ)⟩,
    (drivenNoiseClipPath_norm_le (drivenNoiseClipRadius δ) (drivenNoiseClipRadius_pos δ hδ) N).trans_lt (drivenNoiseClipRadius_lt δ hδ)⟩

theorem drivenNoiseClipSmall_continuous (δ : ℝ) (hδ : 0 < δ) : Continuous (drivenNoiseClipSmall (E := E) δ hδ) :=
  ((drivenNoiseClipPath_continuous (drivenNoiseClipRadius δ) (drivenNoiseClipRadius_pos δ hδ)).subtype_mk _).subtype_mk _

theorem ginibreDrivenPath_clipped_measurable_local_flow (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) :
    ∃ δ : ℝ, ∃ hδ : δ > 0, ∃ τ : ℝ, ∃ hτ : τ > 0,
    ∃ Φ : C(Icc (-1 : ℝ) 1,Configuration n) → C(Icc 0 τ,Configuration n),
      @Measurable _ _ (borel C(Icc (-1 : ℝ) 1,Configuration n))
        (borel C(Icc 0 τ,Configuration n)) Φ ∧
      (∀ N, Φ N ⟨0,⟨le_rfl,hτ.le⟩⟩ = z) ∧
      (∀ N (t : Icc 0 τ), CollisionFree (Φ N t)) ∧
      (∀ N (t : Icc 0 τ), Φ N t = z+
        drivenBoundedNoiseExtension (Configuration n) (drivenNoiseClipSmall δ hδ N).val t+
        ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (Φ N (Set.projIcc 0 τ hτ.le s))) ∧
      ∀ N Q (t : Icc 0 τ),
        (∀ s ∈ Icc 0 (t : ℝ), N (Set.projIcc (-1 : ℝ) 1 (by norm_num) s) =
          Q (Set.projIcc (-1 : ℝ) 1 (by norm_num) s)) → Φ N t = Φ Q t := by
  obtain ⟨δ,hδ,τ,hτ,Ψ,hMeas,hZero,hCF,hEq,hCausal⟩ := ginibreDrivenPath_measurable_local_flow n α z hz
  let Φ := fun N => Ψ (drivenNoiseClipSmall δ hδ N)
  have hΦ : @Measurable _ _ (borel C(Icc (-1 : ℝ) 1,Configuration n))
      (borel C(Icc 0 τ,Configuration n)) Φ :=
    hMeas.comp (drivenNoiseClipSmall_continuous δ hδ).borel_measurable
  refine ⟨δ,hδ,τ,hτ,Φ,hΦ,fun N => hZero _,fun N t => hCF _ t,fun N t => hEq _ t,?_⟩
  intro N Q t hPast
  apply hCausal
  intro s hs
  have h0 := hPast 0 ⟨le_rfl,t.property.1⟩
  simp only [Set.projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1 : ℝ) 1)] at h0
  change drivenNoiseClip (drivenNoiseClipRadius δ) (N _-N _) = drivenNoiseClip (drivenNoiseClipRadius δ) (Q _-Q _)
  rw [hPast s hs,h0]

end
end GinibrePoincare
