module

public import GinibrePoincare.Analysis.GeneralPotentialVandermondeCentered

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem integral_potentialMeasure (n : ℕ) {V : Potential} (hV : Continuous V)
    (g : Configuration n → ℝ) :
    (∫ z, g z ∂potentialMeasure n V) =
      (potentialPartition n V).toReal⁻¹ *
        ∫ z, potentialWeight n V z * g z ∂configurationVolume n := by
  unfold potentialMeasure rawPotentialMeasure
  rw [integral_smul_measure, ENNReal.toReal_inv]
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_potentialDensity n hV)
    (Filter.Eventually.of_forall fun z => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (potentialWeight_nonneg n V _), smul_eq_mul]

theorem potentialVandermonde_weighted_dbarNormSq (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (g : Configuration n → ℂ) (hg : Differentiable ℝ g) (z : Configuration n) :
    (∑ i, Complex.normSq (piComplexDbar i (potentialVandermondeCoefficient n V g) z *
      piPotentialHalfWeight n n V z)) =
      (potentialPartition n V).toReal⁻¹ * potentialWeight n V z * dbarNormSq g z := by
  have he (i : Fin n) : piComplexDbar i (potentialVandermondeCoefficient n V g) z *
      piPotentialHalfWeight n n V z = potentialVandermondeMultiplier n V z * piComplexDbar i g z := by
    rw [piComplexDbar_potentialVandermondeCoefficient V g hg i z]
    change potentialVandermondeCoefficient n V (piComplexDbar i g) z *
      (∏ j, planarPotentialHalfWeight n V (z j)) = _
    exact potentialVandermondeCoefficient_weighted n V _ z
  simp_rw [he, Complex.normSq_mul, piComplexDbar_eq_dbarComponent]
  rw [← Finset.mul_sum, potentialVandermondeMultiplier_normSq n hn hV hfin]
  rfl

theorem potentialVandermonde_weighted_real_gradient (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : Differentiable ℝ f) (z : Configuration n) :
    (∑ i, Complex.normSq (piComplexDbar i (potentialVandermondeCoefficient n V (fun x => (f x : ℂ))) z *
      piPotentialHalfWeight n n V z)) =
      (1 / 4 : ℝ) * ((potentialPartition n V).toReal⁻¹ *
        potentialWeight n V z * realGradientNormSq f z) := by
  have hfc : Differentiable ℝ (fun x => (f x : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hf
  rw [potentialVandermonde_weighted_dbarNormSq n hn hV hfin _ hfc,
    dbarNormSq_ofReal_eq_realGradientNormSq hf]
  ring

theorem potentialVandermonde_weighted_real_energy (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : Differentiable ℝ f) :
    (∫ z, ∑ i, Complex.normSq (piComplexDbar i
      (potentialVandermondeCoefficient n V (fun x => (f x : ℂ))) z *
        piPotentialHalfWeight n n V z) ∂configurationVolume n) =
      (1 / 4 : ℝ) * potentialGradientEnergy n V f := by
  simp_rw [potentialVandermonde_weighted_real_gradient n hn hV hfin f hf]
  rw [integral_const_mul]
  unfold potentialGradientEnergy
  rw [integral_potentialMeasure n hV]
  simp_rw [mul_assoc]
  rw [integral_const_mul]

end
end GinibrePoincare
