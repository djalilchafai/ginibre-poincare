module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitutionFinite
public import GinibrePoincare.Analysis.GinibreBrownianIntegralIntervalIsometry
public import GinibrePoincare.Analysis.GinibreBrownianIntegralCoefficientMesh
public import GinibrePoincare.Analysis.GinibreBrownianIntegralUniformSums

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def brownianFrozenMultiplierMesh {Ω : Type*} (A : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (N M : ℕ) [NeZero (N*M)] : Ω → ℝ :=
  brownianCoefficientSampleMesh (κ := Fin (N*M)) A
    (fun k => itoUniformNNTime T N (k.val/M)) (fun k => itoUniformNNTime T (N*M) k)

/-- Genuine common-grid isometry controls the error when freezing a bounded
adapted multiplier but retaining the actual fine Brownian integrand. -/
theorem brownianFrozenMultiplier_difference_secondMoment_le {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (A u : ℝ≥0 → Ω → ℝ)
    (hA : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (A t))
    (hu : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (u t))
    (C U : ℝ) (hC : 0 ≤ C) (hU : 0 ≤ U)
    (hAb : ∀ t ω, ‖A t ω‖ ≤ C) (hub : ∀ t ω, ‖u t ω‖ ≤ U)
    (T : ℝ≥0) (N M : ℕ) (hN : 0 < N) (hM : 0 < M) :
    letI : NeZero (N*M) := ⟨Nat.ne_of_gt (Nat.mul_pos hN hM)⟩
    (∫ ω, (∑ k : Fin (N*M),
      (A (itoUniformNNTime T N (k.val/M)) ω-A (itoUniformNNTime T (N*M) k) ω)*
        u (itoUniformNNTime T (N*M) k) ω*
        (B j (itoUniformNNTime T (N*M) (k.val+1)) ω-B j (itoUniformNNTime T (N*M) k) ω))^2 ∂P) ≤
      (T : ℝ)*U^2*(∫ ω, (brownianFrozenMultiplierMesh A T N M ω)^2 ∂P) := by
  letI : NeZero (N*M) := ⟨Nat.ne_of_gt (Nat.mul_pos hN hM)⟩
  let s := fun k : Fin (N*M) => itoUniformNNTime T (N*M) k
  let d := fun k : Fin (N*M) => itoUniformNNTime T (N*M) (k.val+1)-s k
  let G := fun k : Fin (N*M) => fun ω =>
    (A (itoUniformNNTime T N (k.val/M)) ω-A (s k) ω)*u (s k) ω
  have hAm (t : ℝ≥0) : Measurable (A t) := (hA t).mono
    ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl
  have hAi (t : ℝ≥0) : MemLp (A t) 2 P := MemLp.of_bound (hAm t).aestronglyMeasurable C
    (Eventually.of_forall (hAb t))
  have hum (t : ℝ≥0) : Measurable (u t) := (hu t).mono
    ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl
  have hG (k : Fin (N*M)) : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (s k)) _ (G k) :=
    (((hA _).mono ((ginibreBrownianAugmentedFiltration B P hB).mono
      (itoUniformNNTime_coarse_le_fine T N M k hM)) le_rfl).sub (hA _)).mul (hu _)
  have hGi (k : Fin (N*M)) : MemLp (G k) 2 P := by
    simpa only [G,mul_comm,Pi.sub_apply] using actualBoundedMultiplier_memLp_two P (u (s k)) _
      (hum _).aestronglyMeasurable ((hAi _).sub (hAi _)) U (hub _)
  have hend (k : Fin (N*M)) : s k+d k = itoUniformNNTime T (N*M) (k.val+1) :=
    add_tsub_cancel_of_le (itoUniformNNTime_mono T (N*M) (Nat.le_succ k.val))
  have hd (k : Fin (N*M)) : (d k : ℝ) = (T : ℝ)/(N*M : ℕ) :=
    itoUniformNNTime_increment_sub_coe T (N*M) k
  have hdisj (i k : Fin (N*M)) (hik : i ≠ k) (_hi : d i ≠ 0) (_hk : d k ≠ 0) :
      s i+d i ≤ s k ∨ s k+d k ≤ s i := by
    rcases lt_or_gt_of_ne hik with h | h
    · exact Or.inl (by rw [hend]; exact itoUniformNNTime_mono T (N*M) (Nat.succ_le_of_lt h))
    · exact Or.inr (by rw [hend]; exact itoUniformNNTime_mono T (N*M) (Nat.succ_le_of_lt h))
  have hmeshI : Integrable (fun ω => (U*brownianFrozenMultiplierMesh A T N M ω)^2) P := by
    simpa only [mul_pow,brownianFrozenMultiplierMesh] using
      (brownianCoefficientSampleMesh_integrable_sq P A hAm _ _ C hC hAb).const_mul (U^2)
  have hbound (k : Fin (N*M)) (ω : Ω) : ‖G k ω‖ ≤ U*brownianFrozenMultiplierMesh A T N M ω := by
    have hh : ‖A (itoUniformNNTime T N (k.val/M)) ω-A (s k) ω‖ ≤
        brownianFrozenMultiplierMesh A T N M ω := Finset.le_sup'
          (f := fun k : Fin (N*M) => ‖A (itoUniformNNTime T N (k.val/M)) ω-A (s k) ω‖)
          (Finset.mem_univ k)
    dsimp only [G]
    rw [norm_mul,mul_comm]
    exact (mul_le_mul_of_nonneg_right (hub _ ω) (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hh hU)
  have hsum : (∑ k : Fin (N*M), (d k : ℝ)) = T := by
    simp only [hd,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    have hnz : ((N*M : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hh := brownianDisjointIntervalSum_secondMoment_le B P hB hind j s d hdisj G hG hGi
    (fun ω => U*brownianFrozenMultiplierMesh A T N M ω) hmeshI hbound
  rw [hsum] at hh
  simpa only [hend,G,s,mul_pow,integral_const_mul,mul_assoc] using hh

/-- Freezing on a finer outer grid has a vanishing actual expected oscillation,
regardless of how fine the inner refinement is chosen. -/
theorem brownianFrozenMultiplierMesh_tendsto_meanSquare {Ω : Type*}
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (A : ℝ≥0 → Ω → ℝ) (hA : ∀ t, Measurable (A t)) (T : ℝ≥0) (m : ℕ → ℕ)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t => A t ω) (Set.Icc 0 T))
    (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ t ω, ‖A t ω‖ ≤ C) :
    Tendsto (fun n => ∫ ω, (brownianFrozenMultiplierMesh A T (n+1) (m n+1) ω)^2 ∂P)
      atTop (𝓝 0) := by
  let a := fun n => fun k : Fin ((n+1)*(m n+1)) => itoUniformNNTime T (n+1) (k.val/(m n+1))
  let b := fun n => fun k : Fin ((n+1)*(m n+1)) => itoUniformNNTime T ((n+1)*(m n+1)) k
  have ha (n : ℕ) (k : Fin ((n+1)*(m n+1))) : a n k ∈ Set.Icc 0 T :=
    (itoUniformNNTime_common_samples_mem T (n+1) (m n+1) k (Nat.succ_pos _) (Nat.succ_pos _) k.is_lt).1
  have hb (n : ℕ) (k : Fin ((n+1)*(m n+1))) : b n k ∈ Set.Icc 0 T :=
    ⟨bot_le,itoUniformNNTime_le_end T _ k (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) k.is_lt.le⟩
  have hd : Tendsto (fun n : ℕ => (T : ℝ)/((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div,mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T : ℝ)
  exact brownianCoefficientSampleMesh_tendsto_meanSquare P (fun n => Fin ((n+1)*(m n+1)))
    A hA T a b ha hb _ hd (fun n k => by
      simpa only [Nat.cast_add,Nat.cast_one] using
        itoUniformNNTime_coarse_dist_le_step T (n+1) (m n+1) k (Nat.succ_pos _))
    hc C hC (fun t _ ω => hbound t ω)

end
end GinibrePoincare
