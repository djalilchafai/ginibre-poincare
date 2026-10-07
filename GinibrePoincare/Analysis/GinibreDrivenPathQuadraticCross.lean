module

public import GinibrePoincare.Analysis.GinibreDrivenPathUniformPartition

@[expose] public section

/-! Continuous noise has zero quadratic cross variation with a locally Lipschitz drift path. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem ginibreUniformQuadraticCross_tendsto_zero (A N : ℝ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0)
    (hA : LipschitzOnWith C A (Icc 0 t)) (hN : Continuous N) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1),
      (A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))*
      (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i))) atTop (𝓝 0) := by
  have hUC : UniformContinuousOn N (Icc 0 t) := isCompact_Icc.uniformContinuousOn_of_continuous hN.continuousOn
  have hmesh : Tendsto (fun n : ℕ => t/((n : ℝ)+1)) atTop (𝓝 0) := by
    have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul t
    simpa only [mul_zero, mul_one_div] using h
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let η := ε/((C : ℝ)*t+1)
  have hden : 0 < (C : ℝ)*t+1 := by positivity
  have hη : 0 < η := div_pos hε hden
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hUC η hη
  obtain ⟨M, hM⟩ := eventually_atTop.mp (hmesh.eventually_lt_const hδ)
  refine ⟨M, ?_⟩
  intro n hn
  have hτ := ginibreUniformTime_mono t ht n
  have hI (i : ℕ) (hi : i ≤ n+1) : ginibreUniformTime t n i ∈ Icc 0 t := by
    constructor
    · simpa only [ginibreUniformTime_zero] using hτ (Nat.zero_le i)
    · simpa only [ginibreUniformTime_end] using hτ hi
  have hstep (i : ℕ) (hi : i ∈ Finset.range (n+1)) :
      ‖(A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))*
        (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i))‖ ≤
          (C : ℝ)*η*(ginibreUniformTime t n (i+1)-ginibreUniformTime t n i) := by
    have hii := Finset.mem_range.mp hi
    have hi0 := hI i (Nat.le_of_lt hii)
    have hi1 := hI (i+1) (Nat.succ_le_of_lt hii)
    have hdt : 0 ≤ ginibreUniformTime t n (i+1)-ginibreUniformTime t n i :=
      sub_nonneg.mpr (hτ (Nat.le_succ i))
    have hd : dist (ginibreUniformTime t n (i+1)) (ginibreUniformTime t n i) < δ := by
      rw [Real.dist_eq, abs_of_nonneg hdt, ginibreUniformTime_increment]
      exact hM n hn
    have hosc : ‖N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i)‖ ≤ η := by
      simpa only [dist_eq_norm] using (hclose _ hi1 _ hi0 hd).le
    have ha := hA.norm_sub_le hi1 hi0
    rw [Real.norm_of_nonneg hdt] at ha
    rw [norm_mul]
    calc
      _ ≤ ((C : ℝ)*(ginibreUniformTime t n (i+1)-ginibreUniformTime t n i))*η :=
        mul_le_mul ha hosc (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [dist_eq_norm, sub_zero]
  calc
    _ ≤ ∑ i ∈ Finset.range (n+1), ‖(A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))*
        (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i))‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range (n+1), (C : ℝ)*η*(ginibreUniformTime t n (i+1)-ginibreUniformTime t n i) :=
      Finset.sum_le_sum hstep
    _ = (C : ℝ)*η*t := by
      rw [← Finset.mul_sum, Finset.sum_range_sub, ginibreUniformTime_end, ginibreUniformTime_zero, sub_zero]
    _ < ε := by
      dsimp [η]
      calc
        _ = ((C : ℝ)*ε*t)/((C : ℝ)*t+1) := by ring
        _ < ε := (div_lt_iff₀ hden).mpr (by nlinarith)

 theorem ginibreUniformQuadraticVariation_add_lipschitz (A N : ℝ → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (C : ℝ≥0)
    (hA : LipschitzOnWith C A (Icc 0 t)) (hAc : Continuous A) (hN : Continuous N) :
    Tendsto (fun n => (∑ i ∈ Finset.range (n+1),
      ((A+N) (ginibreUniformTime t n (i+1))-(A+N) (ginibreUniformTime t n i))^2)-
        (∑ i ∈ Finset.range (n+1),
          (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i))^2))
      atTop (𝓝 0) := by
  have h := (ginibreUniformQuadraticCross_tendsto_zero A N t ht C hA hN).const_mul 2
  have h' := ginibreUniformQuadraticCross_tendsto_zero A A t ht C hA hAc
  have hsum := h.add h'
  simp only [mul_zero, add_zero] at hsum
  convert hsum using 1
  funext n
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.add_apply]
  ring

end
end GinibrePoincare
