module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralL2Completion
public import GinibrePoincare.Analysis.GinibreStochasticMeanSquareInProbability

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- A vanishing actual mean-square comparison transfers an actual L² limit. -/
theorem actualMeanSquareLimit_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S R : ℕ → Ω → ℝ) (I : Ω → ℝ)
    (hS : ∀ n, MemLp (S n) 2 P) (hR : ∀ n, MemLp (R n) 2 P)
    (hI : MemLp I 2 P)
    (hcomp : Tendsto (fun n => ∫ ω, (S n ω-R n ω)^2 ∂P) atTop (𝓝 0))
    (hlim : Tendsto (fun n => ∫ ω, (S n ω-I ω)^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ω, (R n ω-I ω)^2 ∂P) atTop (𝓝 0) := by
  have hle (n : ℕ) : (∫ ω, (R n ω-I ω)^2 ∂P) ≤
      2*(∫ ω, (S n ω-R n ω)^2 ∂P)+2*(∫ ω, (S n ω-I ω)^2 ∂P) := by
    rw [← integral_const_mul,← integral_const_mul,← integral_add]
    · apply integral_mono ((hR n).sub hI).integrable_sq
        ((((hS n).sub (hR n)).integrable_sq.const_mul 2).add
          (((hS n).sub hI).integrable_sq.const_mul 2))
      intro ω
      dsimp only [Pi.add_apply, Pi.sub_apply]
      nlinarith [sq_nonneg (S n ω-R n ω + (S n ω-I ω))]
    · exact (((hS n).sub (hR n)).integrable_sq.const_mul 2)
    · exact (((hS n).sub hI).integrable_sq.const_mul 2)
  apply squeeze_zero (fun n => integral_nonneg fun ω => sq_nonneg _) hle
  simpa using (hcomp.const_mul 2).add (hlim.const_mul 2)

end
end GinibrePoincare
