module

public import GinibrePoincare.Analysis.CorrespondenceLogApproximation
public import Mathlib.Analysis.SpecialFunctions.Pow.Integral

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

def correspondenceLogPotential (z : ℂ) : ℝ := Real.log ‖z‖

theorem correspondenceLogPotential_locallyIntegrable :
    LocallyIntegrable correspondenceLogPotential volume := by
  have hi : LocallyIntegrable (fun z : ℂ => ‖z‖⁻¹) volume := by
    apply locallyIntegrable_of_norm_le_rpow (E := ℂ) (C := (1 : ℝ)) (α := (1 : ℝ))
    · norm_num [Complex.finrank_real_complex]
    · exact ae_of_all _ (fun z => by
        simp [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z)),
          Real.rpow_neg_one])
    · fun_prop
    · norm_num [Complex.finrank_real_complex]
  have hd := continuous_norm.locallyIntegrable.add hi
  apply hd.mono ((Real.measurable_log.comp continuous_norm.measurable).aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖Real.log ‖z‖‖ ≤ ‖‖z‖+‖z‖⁻¹‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (add_nonneg (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _)))]
  by_cases hz : z = 0
  · simp [hz]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have h1 := Real.log_le_sub_one_of_pos hr
    have h2 := Real.log_le_sub_one_of_pos (inv_pos.mpr hr)
    rw [Real.log_inv] at h2
    exact abs_le.mpr ⟨by linarith, by linarith [inv_nonneg.mpr hr.le]⟩

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceLogPotential_locallyIntegrable
