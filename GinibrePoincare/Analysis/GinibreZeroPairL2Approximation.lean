module

public import GinibrePoincare.Analysis.GinibreZeroPairCutoffEnergy
public import GinibrePoincare.Analysis.GinibreWeakSobolevTruncation

@[expose] public section

/-! # Strong L² approximation by zero-pair cutoffs -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Actual zero-pair multiplication preserves weighted L². -/
theorem ginibreZeroPair_mul_memLp {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n m : ℕ) (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) :
    MemLp (fun z => ginibreZeroPairAvoidanceCutoff n m z • f z) 2 (ginibreMeasure n) := by
  apply hf.of_le ((ginibreZeroPairAvoidanceCutoff_smooth n m).continuous.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖ginibreZeroPairAvoidanceCutoff n m z • f z‖ ≤ ‖f z‖
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (ginibreZeroPairAvoidanceCutoff_mem_unit n m z).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (ginibreZeroPairAvoidanceCutoff_mem_unit n m z).2

/-- Weighted squared value errors tend to zero, with no support restriction. -/
theorem ginibreZeroPair_L2_error_tendsto {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] (n : ℕ) (hn : 0 < n) (f : Configuration n → V)
    (hf : MemLp f 2 (ginibreMeasure n)) :
    Tendsto (fun m => ∫ z, ‖ginibreZeroPairAvoidanceCutoff n m z • f z - f z‖ ^ 2
      ∂ginibreMeasure n) atTop (𝓝 0) := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun z => ‖f z‖ ^ 2)
    (fun m => (((ginibreZeroPairAvoidanceCutoff_smooth n m).continuous.aestronglyMeasurable.smul
      hf.aestronglyMeasurable).sub hf.aestronglyMeasurable).norm.pow 2) hi
    (fun m => ae_of_all _ (fun z => by
      change ‖‖ginibreZeroPairAvoidanceCutoff n m z • f z - f z‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have he : ginibreZeroPairAvoidanceCutoff n m z • f z - f z =
          (ginibreZeroPairAvoidanceCutoff n m z - 1) • f z := by rw [sub_smul, one_smul]
      rw [he, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      obtain ⟨h0, h1⟩ := ginibreZeroPairAvoidanceCutoff_mem_unit n m z
      have hb : (ginibreZeroPairAvoidanceCutoff n m z - 1) ^ 2 ≤ 1 := by nlinarith
      simpa using mul_le_mul_of_nonneg_right hb (sq_nonneg ‖f z‖))) ?_
  · simpa using ht
  · filter_upwards [ginibre_ae_phaseRegular n hn] with z hz
    have he : (fun m => ‖ginibreZeroPairAvoidanceCutoff n m z • f z - f z‖ ^ 2) =ᶠ[atTop]
        (fun _ => 0) :=
      (ginibreZeroPairAvoidanceCutoff_eventually_one_gradient_zero n hn z hz).mono
        (fun m hm => by simp [hm.1])
    exact tendsto_const_nhds.congr' he.symm

/-- Actual L² classes obtained by zero-pair multiplication converge strongly. -/
theorem ginibreZeroPair_mul_L2_tendsto {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (n : ℕ) (hn : 0 < n) (u : Lp V 2 (ginibreMeasure n)) :
    Tendsto (fun m => (ginibreZeroPair_mul_memLp n m u (Lp.memLp u)).toLp
      (fun z => ginibreZeroPairAvoidanceCutoff n m z • u z)) atTop (𝓝 u) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (m : ℕ) : dist ((ginibreZeroPair_mul_memLp n m u (Lp.memLp u)).toLp
      (fun z => ginibreZeroPairAvoidanceCutoff n m z • u z)) u =
      Real.sqrt (∫ z, ‖ginibreZeroPairAvoidanceCutoff n m z • u z - u z‖ ^ 2
        ∂ginibreMeasure n) := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    congr 1
    apply integral_congr_ae
    filter_upwards [(ginibreZeroPair_mul_memLp n m u (Lp.memLp u)).coeFn_toLp] with z hz
    rw [hz]
  simp_rw [he]
  simpa using (ginibreZeroPair_L2_error_tendsto n hn u (Lp.memLp u)).sqrt

/-- Bounded compact values times the actual cutoff gradient converge to zero in L². -/
theorem ginibreZeroPair_gradient_L2_tendsto (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : AEStronglyMeasurable f (ginibreMeasure n))
    (hc : HasCompactSupport f) (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Tendsto (fun m => (ginibreZeroPairAvoidanceCutoff_bounded_gradient_memLp
      n hn f hf hc A hA0 hA m).toLp
      (fun z => f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z))
      atTop (𝓝 0) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (m : ℕ) : dist ((ginibreZeroPairAvoidanceCutoff_bounded_gradient_memLp
      n hn f hf hc A hA0 hA m).toLp
      (fun z => f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z)) 0 =
      Real.sqrt (∫ z, ‖f z • ginibreEuclideanGradient
        (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2 ∂ginibreMeasure n) := by
    rw [L2_dist_eq_sqrt_integral_norm_error]
    apply congrArg Real.sqrt
    apply integral_congr_ae
    filter_upwards [(ginibreZeroPairAvoidanceCutoff_bounded_gradient_memLp
      n hn f hf hc A hA0 hA m).coeFn_toLp, Lp.coeFn_zero (E := EuclideanSpace ℝ (Fin n × Fin 2)) (p := 2) (μ := ginibreMeasure n)] with z hz hzero
    change ((0 : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :
      Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) z = 0 at hzero
    rw [hz, hzero, sub_zero]
  simp_rw [he]
  simpa using (ginibreZeroPairAvoidanceCutoff_bounded_gradient_energy_tendsto
    n hn f hf hc A hA0 hA).sqrt
end
end GinibrePoincare
