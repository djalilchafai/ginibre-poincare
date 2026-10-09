module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralUniformLimit
public import GinibrePoincare.Analysis.BrownianIntegralContinuousModificationMartingale

@[expose] public section

/-! A genuine continuous adapted Brownian integral, constructed from the actual left sums. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem brownianContinuousIntegral_exists {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (F t))
    (T : ℝ≥0) (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ω, ‖F t ω‖ ≤ C) :
    ∃ M : ℝ≥0 → Ω → ℝ,
      Martingale M (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => M t ω)) ∧ (∀ t, MemLp (M t) 2 P) ∧
      M 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t, TendstoInMeasure P (fun n => brownianUniformPartialSum (B j) F T (n+1) t) atTop (M t)) ∧
      ∀ t, Tendsto (fun n => ∫ ω, (brownianUniformPartialSum (B j) F T (n+1) t ω-M t ω)^2 ∂P) atTop (𝓝 0) := by
  let hb := fun i => (hB i).toIsPreBrownianReal
  let ℱ := ginibreBrownianAugmentedFiltration B P hb
  have hFi (t : ℝ≥0) : MemLp (F t) 2 P := MemLp.of_bound
    ((hF t).mono (ℱ.le t) le_rfl).aestronglyMeasurable C (Eventually.of_forall (hbound t))
  let S := fun n => brownianUniformPartialSum (B j) F T (n+1)
  have hSM (n : ℕ) : Martingale (S n) ℱ P :=
    brownianUniformPartialSum_martingale B P hb hind j F hF hFi T (n+1)
  have hST (n : ℕ) : MemLp (S n T) 2 P :=
    brownianUniformPartialSum_memLp_two B P hb hind j F hF hFi T (n+1) T
  have hSC (n : ℕ) : ∀ᵐ ω ∂P, ContinuousOn (fun t => S n t ω) (Set.Icc 0 T) :=
    (hB j).cont.mono fun ω hω => (brownianUniformPartialSum_continuous (B j) F T (n+1) ω hω).continuousOn
  have hterm : Tendsto (fun q : ℕ×ℕ => ∫ ω, (S q.2 T ω-S q.1 T ω)^2 ∂P) atTop (𝓝 0) := by
    have hh := brownianUniformPartialSum_tendsto_difference_meanSquare B P hb hind j F hF hFi T T le_rfl hc C hC (fun t _ ω => hbound t ω)
    convert hh using 1
    funext q
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by dsimp [S]; ring)
  obtain ⟨M, hM, hMC, hML, hMP, hMS⟩ := realMartingale_terminal_cauchy_exists_continuous_martingale P ℱ
    (ginibreBrownianFamilyPastSpace B) (ginibreBrownianFamilyPastSpace_le B P hb) (fun t => rfl)
    S hSM T hST hSC (fun n t ω => (brownianUniformPartialSum_time_cap (B j) F T (n+1) t ω).symm) hterm
  have hp0 : TendstoInMeasure P (fun _ : ℕ => (fun _ : Ω => (0 : ℝ))) atTop (M 0) := by
    convert hMP 0 using 1
    funext n ω
    exact (brownianUniformPartialSum_zero (B j) F T (n+1) ω).symm
  have hz : TendstoInMeasure P (fun _ : ℕ => (fun _ : Ω => (0 : ℝ))) atTop (fun _ => 0) :=
    tendstoInMeasure_of_tendsto_ae (fun _ => aestronglyMeasurable_const)
      (Eventually.of_forall fun _ => tendsto_const_nhds)
  exact ⟨M, hM, hMC, hML, tendstoInMeasure_ae_unique hp0 hz, hMP, hMS⟩

end
end GinibrePoincare
