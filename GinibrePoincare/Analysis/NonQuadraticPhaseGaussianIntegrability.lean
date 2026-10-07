module

public import GinibrePoincare.Analysis.NonQuadraticHolomorphicHomogeneity
public import GinibrePoincare.Analysis.GinibreMassFiniteness

@[expose] public section

/-! # Actual Gaussian eligibility of homogeneous entire phase functions -/
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

theorem configuration_one_add_norm_le_prod (n : ℕ) (z : Configuration n) :
    1 + ‖z‖ ≤ ∏ i, (1 + ‖z i‖) := by
  let B := ∏ i : Fin n, (1 + ‖z i‖)
  have hf (i : Fin n) : 1 ≤ 1 + ‖z i‖ := by linarith [norm_nonneg (z i)]
  have hB : 1 ≤ B := Finset.one_le_prod₀ (fun i _ => hf i)
  have hi (i : Fin n) : 1 + ‖z i‖ ≤ B := by
    have he : B = (1 + ‖z i‖) * ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 + ‖z j‖) :=
      (Finset.mul_prod_erase Finset.univ (fun j => 1 + ‖z j‖) (Finset.mem_univ i)).symm
    have ho : 1 ≤ ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (1 + ‖z j‖) :=
      Finset.one_le_prod₀ (fun j _ => hf j)
    rw [he]
    nlinarith [hf i]
  have hz : ‖z‖ ≤ B - 1 := (pi_norm_le_iff_of_nonneg (by linarith)).mpr (fun i => by linarith [hi i])
  linarith

/-- A genuine continuous homogeneous function has actual Gaussian L²
integrability, derived from its compact-sphere polynomial growth. -/
theorem continuous_homogeneous_memLp_complexGaussian {n d : ℕ}
    (F : Configuration n → ℂ) (hF : Continuous F)
    (hh : ∀ (u : ℂ) (z : Configuration n), F (u • z) = u ^ d * F z) :
    MemLp F 2 (complexGaussianMeasure n) := by
  obtain ⟨C, hC, hb⟩ := continuous_homogeneous_polynomial_growth F hF d hh
  apply (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mpr
  apply ((integrable_prod_one_add_norm_pow_const_complexGaussianMeasure n (2 * d)).const_mul (C ^ 2)).mono'
    (hF.norm.pow 2).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro z
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + ‖z‖) (configuration_one_add_norm_le_prod n z) d
  have hf := (hb z).trans (mul_le_mul_of_nonneg_left hp hC)
  have hs := (sq_le_sq₀ (norm_nonneg (F z)) (by positivity : 0 ≤ C * (∏ i, (1 + ‖z i‖)) ^ d)).mpr hf
  rw [mul_pow, ← pow_mul] at hs
  change |‖F z‖ ^ 2| ≤ _
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_comm d 2, Finset.prod_pow] using hs

/-- Entire unit-phase covariance alone supplies the Gaussian square
integrability needed for a Gaussian phase reconstruction argument. -/
theorem entire_phase_memLp_complexGaussian {n d : ℕ}
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F)
    (hp : ∀ (u : ℂ) (z : Configuration n), ‖u‖ = 1 → F (u • z) = u ^ d * F z) :
    MemLp F 2 (complexGaussianMeasure n) :=
  continuous_homogeneous_memLp_complexGaussian F hF.continuous
    (entire_phase_implies_complex_homogeneity F hF d hp)
end
end GinibrePoincare
