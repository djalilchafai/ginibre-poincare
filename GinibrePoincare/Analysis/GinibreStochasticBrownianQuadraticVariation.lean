module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticSums
public import GinibrePoincare.Analysis.GinibreStochasticOURiemann

@[expose] public section

/-! # Actual Brownian quadratic variation along uniform partitions in mean square -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 def ginibreBrownianUniformQuadraticSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  ginibreBrownianQuadraticSum B (n+1) (fun i => ginibreUniformBrownianTime t n i)

 theorem ginibreBrownianUniformTime_increment_coe (t : ℝ≥0) (n i : ℕ) :
    ((ginibreUniformBrownianTime t n (i+1)-ginibreUniformBrownianTime t n i : ℝ≥0) : ℝ) =
      (t : ℝ)/((n : ℝ)+1) := by
  rw [NNReal.coe_sub (ginibreUniformBrownianTime_mono t n (Nat.le_succ i)),
    ginibreUniformBrownianTime_coe, ginibreUniformBrownianTime_coe,
    ginibreUniformTime_increment]

 theorem ginibreBrownianUniformQuadraticSum_mean {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    (∫ ω, ginibreBrownianUniformQuadraticSum B t n ω ∂P) = (t : ℝ) := by
  have h := ginibreBrownianQuadraticSum_mean B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  change (∫ ω, ginibreBrownianUniformQuadraticSum B t n ω ∂P) = _ at h
  simp only [Fin.val_succ, Fin.val_castSucc, ginibreBrownianUniformTime_increment_coe,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  simpa only [mul_div_cancel₀ _ hn] using h

 theorem ginibreBrownianUniformQuadraticSum_variance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    variance (ginibreBrownianUniformQuadraticSum B t n) P = 2*(t : ℝ)^2/((n : ℝ)+1) := by
  have h := ginibreBrownianQuadraticSum_variance B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  change variance (ginibreBrownianUniformQuadraticSum B t n) P = _ at h
  simp only [Fin.val_succ, Fin.val_castSucc, ginibreBrownianUniformTime_increment_coe,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one] at h
  rw [h]
  have hn : (n : ℝ)+1 ≠ 0 := by positivity
  field_simp
  <;> ring

 theorem ginibreBrownianUniformQuadraticSum_meanSquaredError {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (t : ℝ≥0) (n : ℕ) :
    (∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω-(t : ℝ))^2 ∂P) =
      2*(t : ℝ)^2/((n : ℝ)+1) := by
  have hm := ginibreBrownianQuadraticSum_memLp_two B P hB (n+1)
    (fun i => ginibreUniformBrownianTime t n i)
    ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)
  have h := variance_eq_integral hm.aemeasurable
  change variance (ginibreBrownianUniformQuadraticSum B t n) P =
    (∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω - ∫ x, ginibreBrownianUniformQuadraticSum B t n x ∂P)^2 ∂P) at h
  rw [ginibreBrownianUniformQuadraticSum_mean B P hB t n] at h
  exact h.symm.trans (ginibreBrownianUniformQuadraticSum_variance B P hB t n)

 theorem ginibreBrownianUniformQuadraticSum_tendsto_meanSquare {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω-(t : ℝ))^2 ∂P)
      atTop (nhds 0) := by
  simp_rw [ginibreBrownianUniformQuadraticSum_meanSquaredError B P hB t]
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (2*(t : ℝ)^2)
  simpa only [mul_zero, mul_one_div] using h

end
end GinibrePoincare
