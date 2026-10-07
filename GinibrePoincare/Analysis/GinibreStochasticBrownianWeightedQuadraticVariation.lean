module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadraticSum
public import GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticVariation

@[expose] public section

/-! Uniform-partition predictable quadratic errors vanish in actual mean square. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def ginibreBrownianWeightedQuadraticError {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (n : ℕ)
    (F : (i : Fin (n+1)) → (Set.Iic (ginibreUniformBrownianTime t n i) → ℝ) → ℝ) : Ω → ℝ :=
  fun ω => ∑ i, F i (fun v => B v ω)*
    ((B (ginibreUniformBrownianTime t n (i.val+1)) ω-B (ginibreUniformBrownianTime t n i) ω)^2-
      (t : ℝ)/((n : ℝ)+1))

theorem ginibreBrownianWeightedQuadraticError_secondMoment_le {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (t : ℝ≥0) (n : ℕ)
    (F : (i : Fin (n+1)) → (Set.Iic (ginibreUniformBrownianTime t n i) → ℝ) → ℝ)
    (hF : ∀ i, Measurable (F i)) (C : ℝ) (hbound : ∀ i p, ‖F i p‖ ≤ C) :
    (∫ ω, (ginibreBrownianWeightedQuadraticError B t n F ω)^2 ∂P) ≤
      2*C^2*(t : ℝ)^2/((n : ℝ)+1) := by
  let s := fun i : Fin (n+1) => ginibreUniformBrownianTime t n i
  let d := fun i : Fin (n+1) => ginibreUniformBrownianTime t n (i.val+1)-s i
  have hend (i : Fin (n+1)) : s i+d i = ginibreUniformBrownianTime t n (i.val+1) :=
    add_tsub_cancel_of_le (ginibreUniformBrownianTime_mono t n (Nat.le_succ i.val))
  have hc (i j : Fin (n+1)) (hij : i < j) : s i+d i ≤ s j := by
    rw [hend]
    exact ginibreUniformBrownianTime_mono t n (Nat.succ_le_of_lt hij)
  have h := ginibreBrownian_predictable_quadratic_sum_secondMoment_le B P hB
    (n+1) s d hc F hF C hbound
  simp only [hend] at h
  dsimp only [d, s] at h
  simp only [ginibreBrownianUniformTime_increment_coe] at h
  change (∫ ω, (ginibreBrownianWeightedQuadraticError B t n F ω)^2 ∂P) ≤ _ at h
  convert h using 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

theorem ginibreBrownianWeightedQuadraticError_tendsto_meanSquare {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : IsBrownianReal B P) (t : ℝ≥0)
    (F : (n : ℕ) → (i : Fin (n+1)) →
      (Set.Iic (ginibreUniformBrownianTime t n i) → ℝ) → ℝ)
    (hF : ∀ n i, Measurable (F n i)) (C : ℝ) (hbound : ∀ n i p, ‖F n i p‖ ≤ C) :
    Tendsto (fun n => ∫ ω, (ginibreBrownianWeightedQuadraticError B t n (F n) ω)^2 ∂P)
      atTop (nhds 0) := by
  apply squeeze_zero
    (fun n => integral_nonneg fun ω => sq_nonneg _)
    (fun n => ginibreBrownianWeightedQuadraticError_secondMoment_le B P hB t n (F n) (hF n) C (hbound n))
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*C^2*(t : ℝ)^2)
  simpa only [mul_zero, mul_one_div] using h

end
end GinibrePoincare
