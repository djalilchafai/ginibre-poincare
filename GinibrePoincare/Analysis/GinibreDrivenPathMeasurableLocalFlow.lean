module

public import GinibrePoincare.Analysis.GinibreDrivenPathFlowNeighborhood
public import GinibrePoincare.Analysis.GinibreDistributionalGradient

@[expose] public section

/-! An actual measurable and causal local flow for the singular Ginibre equation. -/
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

abbrev drivenSmallNoiseSpace (E : Type*) [NormedAddCommGroup E] (δ : ℝ) :=
  {N : drivenBoundedNoiseSpace E 1 | ‖N.val‖ < δ}

theorem ginibreDrivenPath_measurable_local_flow (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) :
    ∃ δ > (0 : ℝ), ∃ τ : ℝ, ∃ hτ : τ > 0,
    ∃ Ψ : drivenSmallNoiseSpace (Configuration n) δ → C(Icc 0 τ, Configuration n),
      @Measurable _ _ (borel (drivenSmallNoiseSpace (Configuration n) δ))
        (borel C(Icc 0 τ, Configuration n)) Ψ ∧
      (∀ N, Ψ N ⟨0, ⟨le_rfl, hτ.le⟩⟩ = z) ∧
      (∀ N (t : Icc 0 τ), CollisionFree (Ψ N t)) ∧
      (∀ N (t : Icc 0 τ), Ψ N t = z+drivenBoundedNoiseExtension (Configuration n) N.val t+
        ∫ s in (0 : ℝ)..t, ginibreLangevinDrift n α (Ψ N (Set.projIcc 0 τ hτ.le s))) ∧
      ∀ N Q (t : Icc 0 τ),
        (∀ s ∈ Icc 0 (t : ℝ), drivenBoundedNoiseExtension (Configuration n) N.val s =
          drivenBoundedNoiseExtension (Configuration n) Q.val s) → Ψ N t = Ψ Q t := by
  obtain ⟨K, U, hU, hb⟩ := ginibreLangevinDrift_local_lipschitz n α z hz
  obtain ⟨g, hg, heq⟩ := hb.extend_finite_dimension
  obtain ⟨ε, hε, Φ, hLip, hZero, hEq⟩ := drivenContinuousNoise_continuous_local_flow g _ hg z 1 (by norm_num)
  have hUC : U ∩ {x : Configuration n | CollisionFree x} ∈ nhds z :=
    inter_mem hU ((isOpen_collisionFree n).mem_nhds hz)
  obtain ⟨δ, hδ, τ, hτ, hτε, hStay⟩ := drivenContinuousNoise_flow_stays_neighborhood ε hε z Φ
    hLip.continuous hZero _ hUC
  let q : C(Icc 0 τ, Icc 0 ε) :=
    ⟨fun t => ⟨t, ⟨t.property.1, t.property.2.trans hτε⟩⟩,
      continuous_subtype_val.subtype_mk _⟩
  let Ψ : drivenSmallNoiseSpace (Configuration n) δ → C(Icc 0 τ, Configuration n) :=
    fun N => (Φ N.val).comp q
  have hΨ : Continuous Ψ :=
    (ContinuousMap.compCLM (R := ℝ) (Configuration n) q).continuous.comp (hLip.continuous.comp continuous_subtype_val)
  have hRange (N : drivenSmallNoiseSpace (Configuration n) δ) (t : Icc 0 τ) :
      Ψ N t ∈ U ∩ {x : Configuration n | CollisionFree x} :=
    hStay N.val (q t) N.property t.property.2
  refine ⟨δ, hδ, τ, hτ, Ψ, hΨ.borel_measurable,?_,?_,?_,?_⟩
  · intro N
    exact hZero N.val
  · intro N t
    exact (hRange N t).2
  · intro N t
    change Φ N.val (q t) = _
    rw [hEq N.val (q t)]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    change s ∈ uIcc 0 (t : ℝ) at hs
    rw [uIcc_of_le t.property.1] at hs
    have hsτ : s ∈ Icc 0 τ := ⟨hs.1, hs.2.trans t.property.2⟩
    have hsε : s ∈ Icc 0 ε := ⟨hs.1, hsτ.2.trans hτε⟩
    dsimp only
    rw [Set.projIcc_of_mem hε.le hsε, Set.projIcc_of_mem hτ.le hsτ]
    exact (heq (hRange N ⟨s, hsτ⟩).1).symm
  · intro N Q t hPast
    exact drivenContinuousNoise_local_flow_causal g _ hg z 1 ε hε.le Φ hEq N.val Q.val (q t) hPast

end
end GinibrePoincare
