module

public import GinibrePoincare.Analysis.GinibreSpatialCutoffs

@[expose] public section

/-! # Actual derivatives of the combined squared radius of two coordinates -/

open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Squared distance to the set where both selected coordinates vanish. -/
def ginibrePairRadiusSq {n : ℕ} (i j : Fin n) (z : Configuration n) : ℝ :=
  Complex.normSq (z i) + Complex.normSq (z j)

/-- The actual real-linear derivative of one coordinate's squared radius. -/
def coordinateRadiusDerivative {n : ℕ} (z : Configuration n) (i : Fin n) :
    Configuration n →L[ℝ] ℝ :=
  (2 * (z i).re) • (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (2 * (z i).im) • (Complex.imCLM.comp (ContinuousLinearMap.proj i))

theorem hasFDerivAt_coordinateNormSq {n : ℕ} (z : Configuration n) (i : Fin n) :
    HasFDerivAt (fun w : Configuration n => Complex.normSq (w i))
      (coordinateRadiusDerivative z i) z := by
  have hr := Complex.reCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  convert! (hr.mul hr).add (hi.mul hi) using 1
  ext v
  simp [coordinateRadiusDerivative]
  ring

theorem contDiff_coordinateNormSq (n : ℕ) (i : Fin n) :
    ContDiff ℝ ∞ (fun z : Configuration n => Complex.normSq (z i)) := by
  have hr : ContDiff ℝ ∞ (fun z : Configuration n => (z i).re) := Complex.reCLM.contDiff.comp
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  have hi : ContDiff ℝ ∞ (fun z : Configuration n => (z i).im) := Complex.imCLM.contDiff.comp
    (ContinuousLinearMap.proj i : Configuration n →L[ℝ] ℂ).contDiff
  simpa only [Complex.normSq_apply] using (hr.mul hr).add (hi.mul hi)

theorem contDiff_ginibrePairRadiusSq {n : ℕ} (i j : Fin n) :
    ContDiff ℝ ∞ (ginibrePairRadiusSq i j) :=
  (contDiff_coordinateNormSq n i).add (contDiff_coordinateNormSq n j)

theorem ginibrePairRadiusSq_nonneg {n : ℕ} (i j : Fin n) (z : Configuration n) :
    0 ≤ ginibrePairRadiusSq i j z :=
  add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)

theorem ginibrePairRadiusSq_eq_zero_iff {n : ℕ} (i j : Fin n) (z : Configuration n) :
    ginibrePairRadiusSq i j z = 0 ↔ z i = 0 ∧ z j = 0 := by
  rw [ginibrePairRadiusSq, add_eq_zero_iff_of_nonneg (Complex.normSq_nonneg _)
    (Complex.normSq_nonneg _), Complex.normSq_eq_zero, Complex.normSq_eq_zero]

theorem ginibrePairRadiusSq_gradient_real {n : ℕ} (i j k : Fin n) (z : Configuration n) :
    ginibreEuclideanGradient (ginibrePairRadiusSq i j) z (k, 0) =
      (if k = i then 2 * (z i).re else 0) + (if k = j then 2 * (z j).re else 0) := by
  rw [ginibreEuclideanGradient_coordinate,
    show ginibrePairRadiusSq i j = (fun w : Configuration n => Complex.normSq (w i)) +
      (fun w : Configuration n => Complex.normSq (w j)) from rfl,
    ((hasFDerivAt_coordinateNormSq z i).add (hasFDerivAt_coordinateNormSq z j)).fderiv]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [coordinateRadiusDerivative, ginibreCoordinateDirection, realCoordinateDirection,
      coordinateDirection, eq_comm, hi, hj]

theorem ginibrePairRadiusSq_gradient_imag {n : ℕ} (i j k : Fin n) (z : Configuration n) :
    ginibreEuclideanGradient (ginibrePairRadiusSq i j) z (k, 1) =
      (if k = i then 2 * (z i).im else 0) + (if k = j then 2 * (z j).im else 0) := by
  rw [ginibreEuclideanGradient_coordinate,
    show ginibrePairRadiusSq i j = (fun w : Configuration n => Complex.normSq (w i)) +
      (fun w : Configuration n => Complex.normSq (w j)) from rfl,
    ((hasFDerivAt_coordinateNormSq z i).add (hasFDerivAt_coordinateNormSq z j)).fderiv]
  by_cases hi : i = k <;> by_cases hj : j = k <;>
    simp [coordinateRadiusDerivative, ginibreCoordinateDirection, imaginaryCoordinateDirection,
      coordinateDirection, eq_comm, hi, hj]

/-- Distinct coordinate blocks are orthogonal in the actual Euclidean gradient. -/
theorem ginibrePairRadiusSq_gradient_norm_sq {n : ℕ} (i j : Fin n) (hij : i ≠ j)
    (z : Configuration n) :
    ‖ginibreEuclideanGradient (ginibrePairRadiusSq i j) z‖ ^ 2 =
      4 * ginibrePairRadiusSq i j z := by
  classical
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two,
    ginibrePairRadiusSq_gradient_real, ginibrePairRadiusSq_gradient_imag,
    Real.norm_eq_abs, sq_abs]
  have he (k : Fin n) :
      ((if k = i then 2 * (z i).re else 0) + (if k = j then 2 * (z j).re else 0)) ^ 2 +
      ((if k = i then 2 * (z i).im else 0) + (if k = j then 2 * (z j).im else 0)) ^ 2 =
      (if k = i then 4 * Complex.normSq (z i) else 0) +
        (if k = j then 4 * Complex.normSq (z j) else 0) := by
    by_cases hi : k = i
    · subst k; simp [hij, Complex.normSq_apply]; ring
    · by_cases hj : k = j
      · subst k; simp [hij.symm, Complex.normSq_apply]; ring
      · simp [hi, hj]
  simp_rw [he]
  simp [Finset.sum_add_distrib, ginibrePairRadiusSq]
  ring

end
end GinibrePoincare
