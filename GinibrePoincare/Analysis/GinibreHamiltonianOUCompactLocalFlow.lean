module

public import GinibrePoincare.Analysis.GinibreDrivenPathMeasurableLocalFlow
public import GinibrePoincare.Analysis.GinibreDistributionalGradient

@[expose] public section

/-! A genuine collision-free compact local flow for the stationary OU reference. -/
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonianOU_compact_measurable_local_flow (n : ℕ) (α : ℝ) (z : Configuration n)
    (hz : CollisionFree z) :
    ∃ δ > (0 : ℝ), ∃ τ : ℝ, ∃ hτ : τ > 0,
    ∃ K : Set (Configuration n), IsCompact K ∧ (∀ x ∈ K, CollisionFree x) ∧
    ∃ Ψ : drivenSmallNoiseSpace (Configuration n) δ → C(Icc 0 τ, Configuration n),
      @Measurable _ _ (borel (drivenSmallNoiseSpace (Configuration n) δ))
        (borel C(Icc 0 τ, Configuration n)) Ψ ∧
      (∀ N, Ψ N ⟨0,⟨le_rfl,hτ.le⟩⟩ = z) ∧
      (∀ N (t : Icc 0 τ), Ψ N t ∈ K) ∧
      (∀ N (t : Icc 0 τ), Ψ N t = z+drivenBoundedNoiseExtension (Configuration n) N.val t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • (Ψ N (Set.projIcc 0 τ hτ.le s))) ∧
      ∀ N Q (t : Icc 0 τ),
        (∀ s ∈ Icc 0 (t : ℝ), drivenBoundedNoiseExtension (Configuration n) N.val s =
          drivenBoundedNoiseExtension (Configuration n) Q.val s) → Ψ N t = Ψ Q t := by
  let g : Configuration n → Configuration n := fun x => (-2*α/(n : ℝ)) • x
  let gL : Configuration n →L[ℝ] Configuration n := (-2*α/(n : ℝ)) • ContinuousLinearMap.id ℝ (Configuration n)
  have hg : LipschitzWith ‖gL‖₊ g := gL.lipschitz
  obtain ⟨ε,hε,Φ,hLip,hZero,hEq⟩ := drivenContinuousNoise_continuous_local_flow g _ hg z 1 (by norm_num)
  have hUC : {x : Configuration n | CollisionFree x} ∈ nhds z :=
    (isOpen_collisionFree n).mem_nhds hz
  obtain ⟨ρ,hρ,hBall⟩ := Metric.mem_nhds_iff.mp hUC
  let K : Set (Configuration n) := Metric.closedBall z (ρ/2)
  have hK : IsCompact K := isCompact_closedBall z (ρ/2)
  have hKU (x : Configuration n) (hx : x ∈ K) : CollisionFree x := by
    apply hBall
    have hdist : dist x z ≤ ρ/2 := hx
    exact lt_of_le_of_lt hdist (by linarith)
  obtain ⟨δ,hδ,τ,hτ,hτε,hStay⟩ := drivenContinuousNoise_flow_stays_neighborhood ε hε z Φ
    hLip.continuous hZero (Metric.ball z (ρ/2)) (Metric.ball_mem_nhds z (by positivity))
  let q : C(Icc 0 τ,Icc 0 ε) :=
    ⟨fun t => ⟨t,⟨t.property.1,t.property.2.trans hτε⟩⟩,
      continuous_subtype_val.subtype_mk _⟩
  let Ψ : drivenSmallNoiseSpace (Configuration n) δ → C(Icc 0 τ, Configuration n) :=
    fun N => (Φ N.val).comp q
  have hΨ : Continuous Ψ :=
    (ContinuousMap.compCLM (R := ℝ) (Configuration n) q).continuous.comp (hLip.continuous.comp continuous_subtype_val)
  have hRange (N : drivenSmallNoiseSpace (Configuration n) δ) (t : Icc 0 τ) :
      CollisionFree (Ψ N t) :=
    hKU _ (Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hStay N.val (q t) N.property t.property.2)).le)
  refine ⟨δ,hδ,τ,hτ,K,hK,fun x hx => hKU x hx,Ψ,hΨ.borel_measurable,?_,?_,?_,?_⟩
  · intro N
    exact hZero N.val
  · intro N t
    exact Metric.mem_closedBall.mpr (Metric.mem_ball.mp (hStay N.val (q t) N.property t.property.2)).le
  · intro N t
    change Φ N.val (q t) = _
    rw [hEq N.val (q t)]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    change s ∈ uIcc 0 (t : ℝ) at hs
    rw [uIcc_of_le t.property.1] at hs
    have hsτ : s ∈ Icc 0 τ := ⟨hs.1,hs.2.trans t.property.2⟩
    have hsε : s ∈ Icc 0 ε := ⟨hs.1,hsτ.2.trans hτε⟩
    dsimp only
    rw [Set.projIcc_of_mem hε.le hsε, Set.projIcc_of_mem hτ.le hsτ]
    rfl
  · intro N Q t hPast
    exact drivenContinuousNoise_local_flow_causal g _ hg z 1 ε hε.le Φ hEq N.val Q.val (q t) hPast

end
end GinibrePoincare

#print axioms GinibrePoincare.ginibreHamiltonianOU_compact_measurable_local_flow
