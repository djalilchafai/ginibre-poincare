module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralL2Completion
public import GinibrePoincare.Analysis.BrownianIntegralContinuousModificationExistence

@[expose] public section

/-! Almost surely uniform continuous limits of the actual Brownian integral approximations. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem brownianUniformPartialSum_exists_continuous_uniform_limit {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun s => F s ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ s ∈ Set.Icc 0 T, ∀ ω, ‖F s ω‖ ≤ C) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ L : Ω → C(Set.Icc 0 T, ℝ),
      ∀ᵐ ω ∂P, TendstoUniformly (fun n (t : Set.Icc 0 T) => brownianUniformPartialSum (B j) F T (s n+1) t ω)
        (L ω) atTop := by
  let hb := fun i => (hB i).toIsPreBrownianReal
  let S := fun n => brownianUniformPartialSum (B j) F T (n+1)
  have hSM (n : ℕ) : Martingale (S n) (ginibreBrownianAugmentedFiltration B P hb) P :=
    brownianUniformPartialSum_martingale B P hb hind j F hF hFi T (n+1)
  have hST (n : ℕ) : MemLp (S n T) 2 P :=
    brownianUniformPartialSum_memLp_two B P hb hind j F hF hFi T (n+1) T
  have hSC (n : ℕ) : ∀ᵐ ω ∂P, ContinuousOn (fun t => S n t ω) (Set.Icc 0 T) :=
    (hB j).cont.mono fun ω hω => (brownianUniformPartialSum_continuous (B j) F T (n+1) ω hω).continuousOn
  have hterm : Tendsto (fun q : ℕ×ℕ => ∫ ω, (S q.2 T ω-S q.1 T ω)^2 ∂P) atTop (𝓝 0) := by
    have hh := brownianUniformPartialSum_tendsto_difference_meanSquare B P hb hind j F hF hFi T T le_rfl hc C hC hbound
    convert hh using 1
    funext q
    apply integral_congr_ae
    exact Eventually.of_forall (fun ω => by dsimp [S]; ring)
  exact realMartingale_terminal_cauchy_exists_continuous_limit P _ S hSM T hST hSC hterm

end
end GinibrePoincare
