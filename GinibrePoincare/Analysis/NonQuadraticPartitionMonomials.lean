module

public import GinibrePoincare.Analysis.NonQuadraticRadiusLaw
public import GinibrePoincare.Analysis.NonQuadraticWeightedMonomialRepresentatives

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ENNReal ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

theorem planarWeightedMonomial_norm_sq (n k : ℕ) (V : ℂ → ℝ) (z : ℂ) :
    ‖z ^ k * planarPotentialHalfWeight n V z‖ ^ 2 =
      Complex.normSq z ^ k * Real.exp (-(n : ℝ) * V z) := by
  rw [norm_mul, norm_pow]
  unfold planarPotentialHalfWeight
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), mul_pow]
  rw [show (‖z‖ ^ k) ^ 2 = (‖z‖ ^ 2) ^ k by rw [← pow_mul, ← pow_mul, Nat.mul_comm],
    ← Complex.normSq_eq_norm_sq]
  rw [pow_two, ← Real.exp_add]
  congr 2
  ring

theorem potentialPartition_weightedMonomial_memLp (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) (i : Fin n) :
    MemLp (fun z : ℂ => z ^ i.val * planarPotentialHalfWeight n V z) 2 volume := by
  have hmass := (rawPotentialKostlanCoordinateLaw_mass_valid n hn hV hr hfin i).2
  rw [rawPotentialKostlanCoordinateLaw_eq_volume n i.val hn hV,
    Measure.smul_apply, smul_eq_mul] at hmass
  have hc : ENNReal.ofReal ((n : ℝ) / Real.pi) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (by positivity)).ne'
  have hpoly : ((potentialPolynomialVolume i.val).withDensity
      (fun z => ENNReal.ofReal (Real.exp (-(n : ℝ) * V z)))) Set.univ < ⊤ :=
    ENNReal.lt_top_of_mul_ne_top_right hmass.ne hc
  have hexp : Continuous (fun z : ℂ => Real.exp (-(n : ℝ) * V z)) :=
    Real.continuous_exp.comp (continuous_const.mul hV)
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, potentialPolynomialVolume,
    lintegral_withDensity_eq_lintegral_mul (volume : Measure ℂ)
      (f := fun z => ENNReal.ofReal (Complex.normSq z ^ i.val)) (by fun_prop)
      hexp.measurable.ennreal_ofReal] at hpoly
  have hcont : Continuous (fun z : ℂ => z ^ i.val * planarPotentialHalfWeight n V z) := by
    unfold planarPotentialHalfWeight
    exact (continuous_id.pow i.val).mul (Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ((continuous_const.mul hV).div_const 2)))
  apply (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).mpr
  refine ⟨(hcont.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun z => sq_nonneg _))]
  simp_rw [planarWeightedMonomial_norm_sq, ENNReal.ofReal_mul (pow_nonneg (Complex.normSq_nonneg _) _)]
  exact hpoly
end
end GinibrePoincare
