module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedApproximation

@[expose] public section

/-! A two-stage approximation principle for genuine nonnegative errors. -/
open Filter MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

theorem nonnegative_error_tendsto_of_approximation
    (u : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (a : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k) (hbound : ∀ n k, u k ≤ v n k)
    (hv : ∀ n, Tendsto (v n) atTop (𝓝 (a n)))
    (ha : Tendsto a atTop (𝓝 0)) : Tendsto u atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun k => hb.trans_le (hu k)
  · intro b hb
    obtain ⟨n, hn⟩ := (ha.eventually (eventually_lt_nhds hb)).exists
    filter_upwards [(hv n).eventually (eventually_lt_nhds hn)] with k hk
    exact (hbound n k).trans_lt hk

theorem actualMeanSquareLimit_initial_cutoff_transfer {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : ℕ → Ω → ℝ) (A : ℕ → ℕ → Ω → ℝ)
    (M : ℕ → Ω → ℝ) (I : Ω → ℝ)
    (hS : ∀ k, MemLp (S k) 2 P) (hA : ∀ n k, MemLp (A n k) 2 P)
    (hM : ∀ n, MemLp (M n) 2 P) (hI : MemLp I 2 P)
    (e d : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0)) (hd : Tendsto d atTop (𝓝 0))
    (hb : ∀ n k, (∫ ω, (S k ω-A n k ω)^2 ∂P) ≤ e n+d k)
    (hlim : ∀ n, Tendsto (fun k => ∫ ω, (A n k ω-M n ω)^2 ∂P) atTop (𝓝 0))
    (hm : Tendsto (fun n => ∫ ω, (M n ω-I ω)^2 ∂P) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ ω, (S k ω-I ω)^2 ∂P) atTop (𝓝 0) := by
  let v := fun n k => 4*(e n+d k+(∫ ω, (A n k ω-M n ω)^2 ∂P)+
    (∫ ω, (M n ω-I ω)^2 ∂P))
  let a := fun n => 4*(e n+(∫ ω, (M n ω-I ω)^2 ∂P))
  apply nonnegative_error_tendsto_of_approximation _ v a
    (fun k => integral_nonneg fun ω => sq_nonneg _)
  · intro n k
    have hh := actualMeanSquare_difference_le_four_errors P (S k) (A n k) (M n) I I
      (hS k) (hA n k) (hM n) hI hI
    simp only [sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), integral_zero, add_zero] at hh
    exact hh.trans (by dsimp only [v]; gcongr; exact hb n k)
  · intro n
    have hh := (((hd.const_add (e n)).add (hlim n)).add_const
      (∫ ω, (M n ω-I ω)^2 ∂P)).const_mul 4
    simpa only [v, a, add_zero] using hh
  · have hh := (he.add hm).const_mul 4
    simpa only [a, add_zero, mul_zero] using hh

#print axioms actualMeanSquareLimit_initial_cutoff_transfer
#print axioms nonnegative_error_tendsto_of_approximation
end
end GinibrePoincare
