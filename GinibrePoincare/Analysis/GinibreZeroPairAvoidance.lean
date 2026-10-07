module

public import GinibrePoincare.Analysis.GinibreZeroPairCutoff

@[expose] public section

/-! # Symmetric radial cutoffs excluding all simultaneous coordinate zero pairs -/

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

/-- Ordered distinct coordinate pairs. Both orders are included to retain a
simple canonical permutation action. -/
abbrev DistinctCoordinatePair (n : ℕ) := {p : Fin n × Fin n // p.1 ≠ p.2}

/-- The actual product of all pair cutoffs, excluding every simultaneous zero pair. -/
def ginibreZeroPairAvoidanceCutoff (n m : ℕ) (z : Configuration n) : ℝ :=
  ∏ p : DistinctCoordinatePair n, ginibreZeroPairCutoff m p.val.1 p.val.2 z

theorem ginibreZeroPairAvoidanceCutoff_smooth (n m : ℕ) :
    ContDiff ℝ ∞ (ginibreZeroPairAvoidanceCutoff n m) := by
  classical
  apply contDiff_prod
  intro p _
  exact ginibreZeroPairCutoff_smooth m p.val.1 p.val.2

theorem ginibreZeroPairAvoidanceCutoff_mem_unit (n m : ℕ) (z : Configuration n) :
    0 ≤ ginibreZeroPairAvoidanceCutoff n m z ∧ ginibreZeroPairAvoidanceCutoff n m z ≤ 1 := by
  classical
  constructor
  · exact Finset.prod_nonneg (fun p _ => (ginibreZeroPairCutoff_mem_unit m p.val.1 p.val.2 z).1)
  · exact Finset.prod_le_one₀ (fun p _ => (ginibreZeroPairCutoff_mem_unit m p.val.1 p.val.2 z).1)
      (fun p _ => (ginibreZeroPairCutoff_mem_unit m p.val.1 p.val.2 z).2)

theorem ginibreZeroPairAvoidanceCutoff_radial (n m : ℕ) :
    ∃ F : (Fin n → ℝ) → ℝ, ∀ z,
      ginibreZeroPairAvoidanceCutoff n m z = F (fun i => Complex.normSq (z i)) :=
  ⟨fun r => ∏ p : DistinctCoordinatePair n,
    (1 - sobolevCutoffBump (((m : ℝ) + 1) * (r p.val.1 + r p.val.2))), fun _ => rfl⟩

theorem ginibreZeroPairAvoidanceCutoff_symmetric (n m : ℕ) :
    IsSymmetric (ginibreZeroPairAvoidanceCutoff n m) := by
  classical
  intro σ z
  let e : DistinctCoordinatePair n ≃ DistinctCoordinatePair n :=
    Equiv.subtypeEquiv (Equiv.prodCongr σ σ) (fun p => by simp [σ.injective.eq_iff])
  have he (p : DistinctCoordinatePair n) :
      ginibreZeroPairCutoff m p.val.1 p.val.2 (permute σ z) =
        ginibreZeroPairCutoff m (e p).val.1 (e p).val.2 z := rfl
  change (∏ p : DistinctCoordinatePair n,
    ginibreZeroPairCutoff m p.val.1 p.val.2 (permute σ z)) = _
  simp_rw [he]
  exact e.prod_comp (fun p => ginibreZeroPairCutoff m p.val.1 p.val.2 z)

/-- The support of the product lies in the open region where the existing
radial weak-to-smooth approximation theorem applies. -/
theorem ginibreZeroPairAvoidanceCutoff_support_phaseRegular (n : ℕ) (hn : 0 < n) (m : ℕ) :
    tsupport (ginibreZeroPairAvoidanceCutoff n m) ⊆ {z | PhaseRegular n z} := by
  classical
  intro z hz
  apply (phaseRegular_iff_zero_injective n hn z).mpr
  intro i j hi hj
  by_contra hij
  let p : DistinctCoordinatePair n := ⟨(i, j), hij⟩
  have hs : tsupport (ginibreZeroPairAvoidanceCutoff n m) ⊆
      tsupport (ginibreZeroPairCutoff m i j) := by
    apply closure_mono
    intro w hw
    exact (Finset.prod_ne_zero_iff.mp hw) p (Finset.mem_univ p)
  have hr := ginibreZeroPairCutoff_support_bound m i j (hs hz)
  have hp : 0 < 1 / ((m : ℝ) + 1) := by positivity
  change 1 / ((m : ℝ) + 1) ≤ ginibrePairRadiusSq i j z at hr
  simp only [ginibrePairRadiusSq, hi, hj, Complex.normSq_zero, add_zero] at hr
  linarith

/-- The exact Euclidean gradient is the finite product-rule sum. -/
theorem ginibreZeroPairAvoidanceCutoff_gradient (n m : ℕ) (z : Configuration n) :
    ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z =
      ∑ p : DistinctCoordinatePair n,
        (∏ q ∈ Finset.univ.erase p, ginibreZeroPairCutoff m q.val.1 q.val.2 z) •
          ginibreEuclideanGradient (ginibreZeroPairCutoff m p.val.1 p.val.2) z := by
  classical
  ext k
  rw [ginibreEuclideanGradient_coordinate]
  change fderiv ℝ (fun w : Configuration n => ∏ p : DistinctCoordinatePair n,
    ginibreZeroPairCutoff m p.val.1 p.val.2 w) z (ginibreCoordinateDirection k) = _
  rw [fderiv_finsetProd (fun p _ =>
    ((ginibreZeroPairCutoff_smooth m p.val.1 p.val.2).differentiable (by simp)).differentiableAt)]
  simp [ginibreEuclideanGradient_coordinate]

/-- A fixed finite sum of locally integrable inverse radii dominates the actual
squared gradient of every product cutoff. -/
theorem ginibreZeroPairAvoidanceCutoff_gradient_inverse_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n m (z : Configuration n),
      ‖ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2 ≤
        (Fintype.card (DistinctCoordinatePair n) : ℝ) * C *
          ∑ p : DistinctCoordinatePair n, (ginibrePairRadiusSq p.val.1 p.val.2 z)⁻¹ := by
  classical
  obtain ⟨C, hC0, hC⟩ := ginibreZeroPairCutoff_gradient_inverse_bound
  refine ⟨C, hC0, ?_⟩
  intro n m z
  let d (p : DistinctCoordinatePair n) :=
    ginibreEuclideanGradient (ginibreZeroPairCutoff m p.val.1 p.val.2) z
  have hb (p : DistinctCoordinatePair n) :
      ‖∏ q ∈ Finset.univ.erase p, ginibreZeroPairCutoff m q.val.1 q.val.2 z‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg (fun q _ =>
      (ginibreZeroPairCutoff_mem_unit m q.val.1 q.val.2 z).1))]
    exact Finset.prod_le_one₀ (fun q _ => (ginibreZeroPairCutoff_mem_unit m q.val.1 q.val.2 z).1)
      (fun q _ => (ginibreZeroPairCutoff_mem_unit m q.val.1 q.val.2 z).2)
  have hg : ‖ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ≤ ∑ p, ‖d p‖ := by
    rw [ginibreZeroPairAvoidanceCutoff_gradient]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro p _
    rw [norm_smul]
    simpa [d] using mul_le_mul_of_nonneg_right (hb p) (norm_nonneg (d p))
  have hsq : ‖ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2 ≤
      (∑ p, ‖d p‖) ^ 2 := by
    nlinarith [norm_nonneg (ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z),
      Finset.sum_nonneg (s := Finset.univ) (fun p _ => norm_nonneg (d p))]
  have hcs : (∑ p, ‖d p‖) ^ 2 ≤ (Fintype.card (DistinctCoordinatePair n) : ℝ) * ∑ p, ‖d p‖ ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : DistinctCoordinatePair n => (1 : ℝ)) (fun p => ‖d p‖)
  calc
    _ ≤ (Fintype.card (DistinctCoordinatePair n) : ℝ) * ∑ p, ‖d p‖ ^ 2 := hsq.trans hcs
    _ ≤ (Fintype.card (DistinctCoordinatePair n) : ℝ) *
        ∑ p : DistinctCoordinatePair n, C * (ginibrePairRadiusSq p.val.1 p.val.2 z)⁻¹ := by
      gcongr with p
      exact hC n m p.val.1 p.val.2 p.property z
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- At every phase-regular configuration the product and its gradient are
eventually exactly one and zero. -/
theorem ginibreZeroPairAvoidanceCutoff_eventually_one_gradient_zero (n : ℕ) (hn : 0 < n)
    (z : Configuration n) (hz : PhaseRegular n z) :
    ∀ᶠ m : ℕ in atTop, ginibreZeroPairAvoidanceCutoff n m z = 1 ∧
      ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z = 0 := by
  classical
  have hr (p : DistinctCoordinatePair n) : 0 < ginibrePairRadiusSq p.val.1 p.val.2 z := by
    apply lt_of_le_of_ne (ginibrePairRadiusSq_nonneg _ _ z)
    intro he
    have h0 := (ginibrePairRadiusSq_eq_zero_iff p.val.1 p.val.2 z).mp he.symm
    exact p.property ((phaseRegular_iff_zero_injective n hn z).mp hz _ _ h0.1 h0.2)
  have he := eventually_all.mpr (fun p : DistinctCoordinatePair n =>
    ginibreZeroPairCutoff_eventually_one_gradient_zero p.val.1 p.val.2 z (hr p))
  filter_upwards [he] with m hm
  constructor
  · simp [ginibreZeroPairAvoidanceCutoff, fun p => (hm p).1]
  · rw [ginibreZeroPairAvoidanceCutoff_gradient]
    simp [fun p => (hm p).2]

end
end GinibrePoincare
