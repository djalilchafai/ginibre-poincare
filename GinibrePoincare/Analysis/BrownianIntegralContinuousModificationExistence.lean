module

public import GinibrePoincare.Analysis.BrownianIntegralContinuousModificationPaths

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section

/-- Actual continuous martingales which are mean-square Cauchy at the terminal
time admit a deterministic subsequence converging almost surely uniformly to
an actual continuous path. All probability and convergence conclusions are
derived; the hypotheses contain only the original martingales and moments. -/
theorem realMartingale_terminal_cauchy_exists_continuous_limit
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›) (F : ℕ → ℝ≥0 → Ω → ℝ)
    (hF : ∀ n, Martingale (F n) ℱ P) (T : ℝ≥0)
    (hT : ∀ n, MemLp (F n T) 2 P)
    (hc : ∀ n, ∀ᵐ ω ∂P, ContinuousOn (fun t => F n t ω) (Set.Icc 0 T))
    (hterm : Tendsto (fun q : ℕ × ℕ =>
      ∫ ω, (F q.2 T ω-F q.1 T ω)^2 ∂P) atTop (𝓝 0)) :
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ L : Ω → C(Set.Icc 0 T,ℝ),
      ∀ᵐ ω ∂P, TendstoUniformly (fun n (t : Set.Icc 0 T) => F (s n) t ω) (L ω) atTop := by
  let G := fun n => continuousIntervalPathVersion (F n) T
  have hG := continuousIntervalPathVersion_probability_cauchy P ℱ F hF T hT hc hterm
  let d : ℕ → ℝ := fun n => ((1:ℝ)/2)^n
  have hd : ∀ n, 0 < d n := fun n => pow_pos (by norm_num) n
  let p : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (d n)
  have hp : ∀ n, 0 < p n := fun n => ENNReal.ofReal_pos.mpr (hd n)
  have hpsum : (∑' n, p n) ≠ ⊤ := by
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n => (hd n).le) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  obtain ⟨s,hs,hlimit⟩ := continuousProbabilityCauchy_exists_uniform_limit P G hG
    d hd summable_geometric_two p hp hpsum
  refine ⟨s,hs,(fun ω => continuousMartingalePathLimit (fun n => G (s n)) ω),?_⟩
  filter_upwards [hlimit,continuousIntervalPathVersion_sequence_eq_ae P F T hc] with ω hl he
  convert hl using 1
  funext n t
  exact (he (s n) t).symm

end
end GinibrePoincare
