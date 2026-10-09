module

public import GinibrePoincare.Analysis.GinibreHamiltonianRadialGenerator

@[expose] public section

/-! Actual localized radial CIR martingales, constructed from the original Brownian SDE. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000

theorem ginibreBrownian_local_radius_CIR_martingale_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        (pairwiseRadius) (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-
          (pairwiseRadius) z = J t ω+
            ∫ s in (0 : ℝ)..t, (fun x : Configuration n => (4*(α : ℝ)/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius x))
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hf : ContDiffOn ℝ 2 (pairwiseRadius) {x : Configuration n | CollisionFree x} :=
    (ginibre_contDiff_pairwiseRadius n).of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top)) |>.contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hEq, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_martingale_exists hn0 α z hz B P hB hind R hR T (pairwiseRadius) hf
  refine ⟨J, hJM, hJC, hJL, hJ0,?_⟩
  filter_upwards [hEq] with ω hω
  intro t ht
  rw [hω t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact ginibreRealPaperSpeedGenerator_pairwiseRadius hn α _
    (ginibreBrownianHamiltonianStoppedProcess_range hn0 α z hz B R hR T s.toNNReal ω).1

theorem ginibreBrownian_local_radius_square_CIR_martingale_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        ((fun x : Configuration n => pairwiseRadius x^2)) (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-
          ((fun x : Configuration n => pairwiseRadius x^2)) z = J t ω+
            ∫ s in (0 : ℝ)..t, (fun x : Configuration n => 2*pairwiseRadius x*((4*(α : ℝ)/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius x))+(8*(α : ℝ)/(n : ℝ))*pairwiseRadius x)
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hf : ContDiffOn ℝ 2 ((fun x : Configuration n => pairwiseRadius x^2)) {x : Configuration n | CollisionFree x} :=
    ((ginibre_contDiff_pairwiseRadius n).pow 2).of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top)) |>.contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hEq, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_martingale_exists hn0 α z hz B P hB hind R hR T ((fun x : Configuration n => pairwiseRadius x^2)) hf
  refine ⟨J, hJM, hJC, hJL, hJ0,?_⟩
  filter_upwards [hEq] with ω hω
  intro t ht
  rw [hω t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact ginibreRealPaperSpeedGenerator_pairwiseRadius_square hn α _
    (ginibreBrownianHamiltonianStoppedProcess_range hn0 α z hz B R hR T s.toNNReal ω).1

theorem ginibreBrownian_local_center_CIR_martingale_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        (ginibreCenterSquared n) (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-
          (ginibreCenterSquared n) z = J t ω+
            ∫ s in (0 : ℝ)..t, (fun x : Configuration n => (4*(α : ℝ)/(n : ℝ))*(1-ginibreCenterSquared n x))
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) := by
  have hn0 : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn
  have hf : ContDiffOn ℝ 2 (ginibreCenterSquared n) {x : Configuration n | CollisionFree x} :=
    (contDiff_ginibreCenterSquared n).of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top)) |>.contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hEq, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_martingale_exists hn0 α z hz B P hB hind R hR T (ginibreCenterSquared n) hf
  refine ⟨J, hJM, hJC, hJL, hJ0,?_⟩
  filter_upwards [hEq] with ω hω
  intro t ht
  rw [hω t ht]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  exact ginibreRealPaperSpeedGenerator_centerSquared hn α _
    (ginibreBrownianHamiltonianStoppedProcess_range hn0 α z hz B R hR T s.toNNReal ω).1

end
end GinibrePoincare
