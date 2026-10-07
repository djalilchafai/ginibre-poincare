module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralIsometry
public import GinibrePoincare.Analysis.GinibreBrownianIntegralCoefficientMesh
public import GinibrePoincare.Analysis.FiniteDimensionalItoUniformRefinement

@[expose] public section

/-! Genuine common-refinement second moments for Brownian left sums. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def brownianUniformLeftSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (N : ℕ) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, F (itoUniformNNTime T N i) ω*
    (B (itoUniformNNTime T N (i+1)) ω-B (itoUniformNNTime T N i) ω)

theorem brownianUniformLeftSum_difference_secondMoment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    (∫ ω, (brownianUniformLeftSum (B j) F T N ω-brownianUniformLeftSum (B j) F T M ω)^2 ∂P) =
      (T : ℝ)/(N*M : ℕ)*∑ k : Fin (N*M), ∫ ω,
        (F (itoUniformNNTime T N (k.val/M)) ω-F (itoUniformNNTime T M (k.val/N)) ω)^2 ∂P := by
  let s := fun k : Fin (N*M) => itoUniformNNTime T (N*M) k
  let d := fun k : Fin (N*M) => itoUniformNNTime T (N*M) (k.val+1)-s k
  let G := fun k : Fin (N*M) => fun ω =>
    F (itoUniformNNTime T N (k.val/M)) ω-F (itoUniformNNTime T M (k.val/N)) ω
  have hend (k : Fin (N*M)) : s k+d k = itoUniformNNTime T (N*M) (k.val+1) :=
    add_tsub_cancel_of_le (itoUniformNNTime_mono T (N*M) (Nat.le_succ k.val))
  have hd (k : Fin (N*M)) : (d k : ℝ) = (T : ℝ)/(N*M : ℕ) :=
    itoUniformNNTime_increment_sub_coe T (N*M) k
  have hG (k : Fin (N*M)) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s k)) _ (G k) := by
    have hc1 := itoUniformNNTime_coarse_le_fine T N M k hM
    have hc2 := itoUniformNNTime_coarse_le_fine T M N k hN
    rw [Nat.mul_comm M N] at hc2
    exact ((hF _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono hc1) le_rfl).sub
      ((hF _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono hc2) le_rfl)
  have hchron (i k : Fin (N*M)) (hik : i < k) : s i+d i ≤ s k := by
    rw [hend]
    exact itoUniformNNTime_mono T (N*M) (Nat.succ_le_of_lt hik)
  have hh := ginibreBrownian_augmented_linear_sum_isometry B P hB hind j (N*M) s d hchron G hG
    (fun k => (hFi _).sub (hFi _))
  simp only [hend,hd,← Finset.mul_sum] at hh
  rw [← hh]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  dsimp only
  congr 1
  simp only [brownianUniformLeftSum]
  rw [
    itoUniformNNWeightedSum_difference_common_grid (fun t => F t ω) (fun t => F t ω) (fun t => B j t ω) T N M hN hM]
  simpa only [G,s] using (Fin.sum_univ_eq_sum_range (fun k =>
    (F (itoUniformNNTime T N (k/M)) ω-F (itoUniformNNTime T M (k/N)) ω)*
      (B j (itoUniformNNTime T (N*M) (k+1)) ω-B j (itoUniformNNTime T (N*M) k) ω)) (N*M)).symm

end
end GinibrePoincare
