module

public import GinibrePoincare.Analysis.GinibreDrivenPathContinuousLocalFlow

@[expose] public section

/-! Continuous noise selection stays locally in any prescribed configuration neighborhood. -/
open Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem drivenContinuousNoise_flow_stays_neighborhood
    (ε : ℝ) (hε : 0 < ε) (z : E)
    (Φ : drivenBoundedNoiseSpace E 1 → C(Icc 0 ε,E)) (hΦ : Continuous Φ)
    (hZero : ∀ N, Φ N ⟨0,⟨le_rfl,hε.le⟩⟩ = z)
    (U : Set E) (hU : U ∈ nhds z) :
    ∃ δ > (0 : ℝ), ∃ τ > (0 : ℝ), τ ≤ ε ∧
      ∀ N (t : Icc 0 ε), ‖N.val‖ < δ → (t : ℝ) ≤ τ → Φ N t ∈ U := by
  let N₀ : drivenBoundedNoiseSpace E 1 := ⟨0, by simp⟩
  let t₀ : Icc 0 ε := ⟨0,⟨le_rfl,hε.le⟩⟩
  have hEval : Continuous (fun p : drivenBoundedNoiseSpace E 1 × Icc 0 ε => Φ p.1 p.2) :=
    continuous_eval.comp ((hΦ.comp continuous_fst).prodMk continuous_snd)
  have hPre : (fun p : drivenBoundedNoiseSpace E 1 × Icc 0 ε => Φ p.1 p.2) ⁻¹' U ∈
      nhds (N₀,t₀) := hEval.continuousAt.preimage_mem_nhds (by simpa [t₀,hZero] using hU)
  obtain ⟨V,hV,W,hW,hVW⟩ := mem_nhds_prod_iff.mp hPre
  obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨r,hr,hrW⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨δ,hδ,min ε (r/2),lt_min hε (by positivity),min_le_left _ _,?_⟩
  intro N t hN ht
  apply hVW (a := (N,t))
  constructor
  · apply hδV
    simpa [Metric.mem_ball,Subtype.dist_eq,dist_eq_norm,N₀] using hN
  · apply hrW
    have htr : (t : ℝ) < r := lt_of_le_of_lt (ht.trans (min_le_right _ _)) (by linarith)
    simpa [Metric.mem_ball,Subtype.dist_eq,dist_eq_norm,t₀,Real.norm_of_nonneg t.property.1] using htr

end
end GinibrePoincare
