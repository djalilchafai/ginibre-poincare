module

public import GinibrePoincare.Analysis.GinibreIntegrationByParts
public import GinibrePoincare.Analysis.GinibreDrivenPathDriftRegularity

@[expose] public section

/-! The actual logarithmic Ginibre Hamiltonian, smooth away from collisions. -/
open scoped BigOperators ContDiff ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Logarithmic repulsion with the normalization of the actual Langevin drift. -/
def ginibreHamiltonian (n : ℕ) (z : Configuration n) : ℝ :=
  (n : ℝ) * configurationNormSq z - Real.log (vandermondeWeight z)

theorem contDiff_vandermondeWeight (n : ℕ) :
    ContDiff ℝ ∞ (vandermondeWeight : Configuration n → ℝ) := by
  have hr := Complex.reCLM.contDiff.comp (contDiff_vandermonde n)
  have hi := Complex.imCLM.contDiff.comp (contDiff_vandermonde n)
  convert! (hr.mul hr).add (hi.mul hi) using 1

theorem vandermondeWeight_pos_of_collisionFree {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) : 0 < vandermondeWeight z := by
  apply lt_of_le_of_ne (Complex.normSq_nonneg _)
  exact Ne.symm (fun h => ((collisionFree_iff_not_mem_collisionSet z).mp hz) ((vandermondeWeight_eq_zero_iff z).mp h))

theorem ginibreHamiltonian_contDiffAt (n : ℕ) (z : Configuration n)
    (hz : CollisionFree z) : ContDiffAt ℝ ∞ (ginibreHamiltonian n) z := by
  exact ((contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Configuration n => (n : ℝ)) z).mul (contDiff_configurationNormSq (n := n)).contDiffAt).sub
    ((contDiff_vandermondeWeight n).contDiffAt.log
      (ne_of_gt (vandermondeWeight_pos_of_collisionFree z hz)))

theorem ginibreHamiltonian_exp_neg {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) : Real.exp (-ginibreHamiltonian n z) = ginibreWeight n z := by
  unfold ginibreHamiltonian ginibreWeight gaussianWeight
  rw [neg_sub, Real.exp_sub, Real.exp_log (vandermondeWeight_pos_of_collisionFree z hz)]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  ring

theorem fderiv_ginibreHamiltonian_coordinate {n : ℕ} (z : Configuration n)
    (hz : CollisionFree z) (j : Fin n) (w : ℂ) :
    fderiv ℝ (ginibreHamiltonian n) z (coordinateDirection j w) =
      (n : ℝ) * fderiv ℝ configurationNormSq z (coordinateDirection j w) -
        2 * (∑ k ∈ Finset.univ.erase j, w / (z j - z k)).re := by
  have hs : DifferentiableAt ℝ configurationNormSq z := ((contDiff_configurationNormSq (n := n)).differentiable (by simp)).differentiableAt
  have hv : DifferentiableAt ℝ vandermondeWeight z := ((contDiff_vandermondeWeight n).differentiable (by simp)).differentiableAt
  have hp := vandermondeWeight_pos_of_collisionFree z hz
  unfold ginibreHamiltonian
  rw [fderiv_fun_sub (hs.const_mul _) (hv.log (ne_of_gt hp)), fderiv_const_mul hs,
    fderiv.log hv (ne_of_gt hp)]
  simp only [sub_apply, smul_apply, smul_eq_mul]
  rw [fderiv_vandermondeWeight_apply_coordinateDirection z hz j w]
  field_simp

theorem fderiv_configurationNormSq_coordinate {n : ℕ} (z : Configuration n)
    (j : Fin n) (w : ℂ) :
    fderiv ℝ configurationNormSq z (coordinateDirection j w) =
      2 * (conj (z j) * w).re := by
  rw [fderiv_configurationNormSq_apply]
  congr 1
  unfold coordinateDirection
  rw [Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [hbj]
  · simp

theorem fderiv_ginibreHamiltonian_realCoordinate {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreHamiltonian n) z (realCoordinateDirection j) =
      (n : ℝ) * ginibreRealDriftCoordinate n j z := by
  rw [show realCoordinateDirection j = coordinateDirection j 1 from rfl,
    fderiv_ginibreHamiltonian_coordinate z hz j 1,
    fderiv_configurationNormSq_coordinate]
  simp only [mul_one, Complex.conj_re, one_div]
  rw [show (∑ k ∈ Finset.univ.erase j, (z j-z k)⁻¹).re =
      ∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).re by
    exact map_sum Complex.reCLM _ _]
  unfold ginibreRealDriftCoordinate
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  <;> ring

theorem fderiv_ginibreHamiltonian_imaginaryCoordinate {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z) (j : Fin n) :
    fderiv ℝ (ginibreHamiltonian n) z (imaginaryCoordinateDirection j) =
      (n : ℝ) * ginibreImagDriftCoordinate n j z := by
  rw [show imaginaryCoordinateDirection j = coordinateDirection j Complex.I from rfl,
    fderiv_ginibreHamiltonian_coordinate z hz j Complex.I,
    fderiv_configurationNormSq_coordinate]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.I_re,
    Complex.I_im, mul_zero, mul_one, zero_sub, neg_neg]
  simp_rw [div_eq_mul_inv]
  rw [show (∑ k ∈ Finset.univ.erase j, Complex.I * (z j-z k)⁻¹).re =
      -(∑ k ∈ Finset.univ.erase j, ((z j-z k)⁻¹).im) by
    change Complex.reCLM (∑ k ∈ Finset.univ.erase j, Complex.I * (z j-z k)⁻¹) = _
    rw [map_sum Complex.reCLM]
    simp [Complex.mul_re, Finset.sum_neg_distrib]]
  unfold ginibreImagDriftCoordinate
  have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  field_simp
  <;> ring

end
end GinibrePoincare
