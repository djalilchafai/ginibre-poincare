module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUReversibility
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem gaussianOU_ennreal_pdf_balance (a : ℝ) (v : ℝ≥0) (hv : v ≠ 0)
    (hvar : a^2+2*(v : ℝ)=1) (x y : ℝ) :
    gaussianPDF 0 (1/2) x*gaussianPDF (a*x) v y =
      gaussianPDF 0 (1/2) y*gaussianPDF (a*y) v x := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _),
    gaussianOU_pdf_balance a v hv hvar x y]

theorem ginibreOUTransition_detailed_balance_positive (rate t : ℝ≥0)
    (hv : ginibreOUVariance rate t ≠ 0) (s u : Set ℝ)
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    (∫⁻ x in s, ginibreOUTransition rate t x u ∂gaussianReal 0 (1/2)) =
      ∫⁻ y in u, ginibreOUTransition rate t y s ∂gaussianReal 0 (1/2) := by
  have hhalf : (1/2 : ℝ≥0) ≠ 0 := by norm_num
  have hvar : ginibreOUDecay rate t^2+2*(ginibreOUVariance rate t : ℝ)=1 := by
    rw [ginibreOUVariance_coe]
    ring
  have hpdf : Measurable (fun p : ℝ × ℝ => gaussianPDF 0 (1/2) p.1*
      gaussianPDF (ginibreOUDecay rate t*p.1) (ginibreOUVariance rate t) p.2) :=
    ((measurable_gaussianPDF _ _).comp measurable_fst).mul
      (measurable_uncurry_gaussianPDF.comp
        ((measurable_const.mul measurable_fst).prodMk (measurable_const.prodMk measurable_snd)))
  rw [gaussianReal_of_var_ne_zero _ hhalf,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF _ _)
      ((ginibreOUTransition rate t).measurable_coe hu) hs,
    setLIntegral_withDensity_eq_setLIntegral_mul _ (measurable_gaussianPDF _ _)
      ((ginibreOUTransition rate t).measurable_coe hs) hu]
  change (∫⁻ x in s, gaussianPDF 0 (1/2) x*gaussianReal (ginibreOUDecay rate t*x) (ginibreOUVariance rate t) u) =
    ∫⁻ y in u, gaussianPDF 0 (1/2) y*gaussianReal (ginibreOUDecay rate t*y) (ginibreOUVariance rate t) s
  simp_rw [gaussianReal_apply _ hv]
  simp_rw [← lintegral_const_mul (gaussianPDF 0 (1/2) _) (measurable_gaussianPDF _ _)]
  rw [lintegral_lintegral_swap (hpdf.aemeasurable.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self))]
  apply lintegral_congr
  intro y
  apply lintegral_congr
  intro x
  exact gaussianOU_ennreal_pdf_balance _ _ hv hvar x y

theorem ginibreOUTransition_detailed_balance (rate t : ℝ≥0) (s u : Set ℝ)
    (hs : MeasurableSet s) (hu : MeasurableSet u) :
    (∫⁻ x in s, ginibreOUTransition rate t x u ∂gaussianReal 0 (1/2)) =
      ∫⁻ y in u, ginibreOUTransition rate t y s ∂gaussianReal 0 (1/2) := by
  classical
  by_cases hv : ginibreOUVariance rate t=0
  · have ha : ginibreOUDecay rate t=1 := by
      have hvar := ginibreOUVariance_coe rate t
      rw [hv,NNReal.coe_zero] at hvar
      have hpos := ginibreOUDecay_nonneg rate t
      nlinarith
    have hK (x : ℝ) : ginibreOUTransition rate t x=Measure.dirac x := by
      change gaussianReal (ginibreOUDecay rate t*x) (ginibreOUVariance rate t)=Measure.dirac x
      simp only [hv,ha,one_mul,gaussianReal_zero_var]
    simp_rw [hK,Measure.dirac_apply' _ hu,Measure.dirac_apply' _ hs]
    change (∫⁻ x in s, u.indicator (fun _ => (1 : ℝ≥0∞)) x ∂gaussianReal 0 (1/2))=
      ∫⁻ x in u, s.indicator (fun _ => (1 : ℝ≥0∞)) x ∂gaussianReal 0 (1/2)
    rw [setLIntegral_indicator hu,setLIntegral_indicator hs,inter_comm s u]
  · exact ginibreOUTransition_detailed_balance_positive rate t hv s u hs hu

theorem ginibreOU_stationary_pair_law_reversal (rate t : ℝ≥0) :
    ((gaussianReal 0 (1/2)) ⊗ₘ ginibreOUTransition rate t).map Prod.swap =
      (gaussianReal 0 (1/2)) ⊗ₘ ginibreOUTransition rate t := by
  apply Measure.ext_prod
  intro s u hs hu
  rw [Measure.map_apply measurable_swap (hs.prod hu)]
  have he : Prod.swap ⁻¹' (s ×ˢ u)=u ×ˢ s := by ext p; simp [and_comm]
  rw [he,Measure.compProd_apply_prod hu hs,Measure.compProd_apply_prod hs hu]
  exact ginibreOUTransition_detailed_balance rate t u s hu hs


end
end GinibrePoincare
