module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticVariation

@[expose] public section

/-! A genuine Brownian Itô square identity obtained from actual left sums. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem ginibre_finite_square_increment_identity (x : ℕ → ℝ) (N : ℕ) :
    2*(∑ i ∈ Finset.range N, x i*(x (i+1)-x i))+
      (∑ i ∈ Finset.range N, (x (i+1)-x i)^2) = (x N)^2-(x 0)^2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    simp only [Finset.sum_range_succ]
    nlinarith

def ginibreBrownianItoSquareLeftSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (n : ℕ) : Ω → ℝ := fun ω =>
  ∑ i : Fin (n+1), B (ginibreUniformBrownianTime t n i) ω*
    (B (ginibreUniformBrownianTime t n (i.val+1)) ω-B (ginibreUniformBrownianTime t n i) ω)

theorem ginibreBrownianItoSquareLeftSum_identity {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (n : ℕ) (ω : Ω) :
    2*ginibreBrownianItoSquareLeftSum B t n ω+ginibreBrownianUniformQuadraticSum B t n ω =
      (B t ω)^2-(B 0 ω)^2 := by
  have h := ginibre_finite_square_increment_identity (fun i => B (ginibreUniformBrownianTime t n i) ω) (n+1)
  dsimp [ginibreBrownianItoSquareLeftSum, ginibreBrownianUniformQuadraticSum,
    ginibreBrownianQuadraticSum]
  rw [Fin.sum_univ_eq_sum_range (fun i => B (ginibreUniformBrownianTime t n i) ω * (B (ginibreUniformBrownianTime t n (i+1)) ω-B (ginibreUniformBrownianTime t n i) ω)),
    Fin.sum_univ_eq_sum_range (fun i => (B (ginibreUniformBrownianTime t n (i+1)) ω-B (ginibreUniformBrownianTime t n i) ω)^2)]
  convert h using 1 <;> simp [ginibreUniformBrownianTime, ginibreUniformTime, mul_div_cancel_right₀ _ (show (n : ℝ)+1 ≠ 0 by positivity)]

theorem ginibreBrownianItoSquareLeftSum_meanSquaredError {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) (n : ℕ) :
    (∫ ω, (ginibreBrownianItoSquareLeftSum B t n ω-((B t ω)^2-(t : ℝ))/2)^2 ∂P) =
      (t : ℝ)^2/(2*((n : ℝ)+1)) := by
  have hAE : (fun ω => (ginibreBrownianItoSquareLeftSum B t n ω-((B t ω)^2-(t : ℝ))/2)^2) =ᵐ[P]
      (fun ω => (1/4 : ℝ)*(ginibreBrownianUniformQuadraticSum B t n ω-(t : ℝ))^2) := by
    filter_upwards [hB.eval_zero_ae_eq_zero] with ω hzero
    have h := ginibreBrownianItoSquareLeftSum_identity B t n ω
    rw [hzero] at h
    have hx : ginibreBrownianItoSquareLeftSum B t n ω = ((B t ω)^2-ginibreBrownianUniformQuadraticSum B t n ω)/2 := by nlinarith
    rw [hx]
    ring
  rw [integral_congr_ae hAE, integral_const_mul,
    ginibreBrownianUniformQuadraticSum_meanSquaredError B P hB t n]
  field_simp
  <;> ring

theorem ginibreBrownianItoSquareLeftSum_tendsto_meanSquare {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (ginibreBrownianItoSquareLeftSum B t n ω-((B t ω)^2-(t : ℝ))/2)^2 ∂P)
      atTop (nhds 0) := by
  have h := (ginibreBrownianUniformQuadraticSum_tendsto_meanSquare B P hB t).const_mul (1/4 : ℝ)
  have hEq (n : ℕ) :
      (∫ ω, (ginibreBrownianItoSquareLeftSum B t n ω-((B t ω)^2-(t : ℝ))/2)^2 ∂P) =
        (1/4 : ℝ)*(∫ ω, (ginibreBrownianUniformQuadraticSum B t n ω-(t : ℝ))^2 ∂P) := by
    rw [ginibreBrownianItoSquareLeftSum_meanSquaredError B P hB t n,
      ginibreBrownianUniformQuadraticSum_meanSquaredError B P hB t n]
    field_simp
    <;> ring
  simp_rw [hEq]
  simpa only [mul_zero] using h

end
end GinibrePoincare
