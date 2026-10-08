module
public import GinibrePoincare.Analysis.CorrespondencePolynomialRealGaussian
public import GinibrePoincare.Analysis.FinitePiDensity
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option linter.style.haveILetI false

/-- Gaussian polynomial moments written against literal real-coordinate
Lebesgue density, with arbitrary positive variance. -/
theorem correspondencePolynomial_realGaussian_density_integrable {ι : Type*}
    [Fintype ι] [DecidableEq ι] (v : ℝ≥0) (hv : v≠0) (P : MvPolynomial ι ℝ) :
    Integrable (fun x : ι → ℝ => Real.exp (-(∑ i, (x i)^2)/(2*(v:ℝ))) * MvPolynomial.eval x P) volume := by
  let μ : Measure (ι → ℝ) := Measure.pi (fun _ : ι => gaussianReal 0 v)
  have hi : Integrable (fun x => MvPolynomial.eval x P) μ := by
    have he : (fun x => MvPolynomial.eval x P) = fun x =>
        ∑ d ∈ P.support, MvPolynomial.eval x (MvPolynomial.monomial d (P.coeff d)) := by
      funext x
      conv_lhs => rw [P.as_sum]
      simp only [map_sum]
    rw [he]
    apply integrable_finsetSum
    intro d hd
    have hnorm : Integrable (fun x : ι→ℝ => ∏ i, ‖x i‖^(d i)) μ := by
      unfold μ
      apply Integrable.fintype_prod (f := fun i (y : ℝ) => ‖y‖^(d i))
      intro i
      exact (IsGaussian.memLp_id (gaussianReal 0 v) ((d i : ℕ) : ℝ≥0∞) (by finiteness)).integrable_norm_pow'
    apply (integrable_norm_iff (MvPolynomial.continuous_eval _).aestronglyMeasurable).mp
    convert hnorm.const_mul (‖P.coeff d‖) using 1
    funext x
    simp only [MvPolynomial.eval_monomial,norm_mul]
    rw [Finsupp.prod_fintype _ _ (by intro i; simp)]
    simp only [norm_prod,norm_pow]
  letI : SigmaFinite ((volume : Measure ℝ).withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  have hμ : μ = (volume : Measure (ι→ℝ)).withDensity
      (fun x => ∏ i, gaussianPDF 0 v (x i)) := by
    unfold μ
    rw [show (fun _ : ι => gaussianReal 0 v) =
      (fun _ : ι => (volume : Measure ℝ).withDensity (gaussianPDF 0 v)) by
      funext i; exact gaussianReal_of_var_ne_zero 0 hv]
    rw [Measure.pi_withDensity _ _ (fun _ => measurable_gaussianPDF 0 v), ← volume_pi]
  rw [hμ] at hi
  have hprod (x : ι→ℝ) : (∏ i, gaussianPDF 0 v (x i)).toReal =
      ((Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹)^(Fintype.card ι) *
        Real.exp (-(∑ i, (x i)^2)/(2*(v:ℝ))) := by
    simp only [ENNReal.toReal_prod,gaussianPDF]
    simp only [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
    simp only [gaussianPDFReal,sub_zero]
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,← Real.exp_sum]
    congr 2
    rw [← Finset.sum_div,← Finset.sum_neg_distrib]
  have he := (integrable_withDensity_iff
    (by fun_prop : Measurable (fun x : ι→ℝ => ∏ i, gaussianPDF 0 v (x i)))
    (ae_of_all _ fun x => ENNReal.prod_lt_top (fun i _ => gaussianPDF_lt_top))).mp hi
  simp only [hprod] at he
  have hc : ((Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹)^(Fintype.card ι) ≠ 0 := by
    apply pow_ne_zero
    apply inv_ne_zero
    apply Real.sqrt_ne_zero'.mpr
    have hvR : 0<(v:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
    positivity
  have hmul : Integrable (fun x : ι→ℝ => ((Real.sqrt (2*Real.pi*(v:ℝ)))⁻¹)^(Fintype.card ι) *
      (Real.exp (-(∑ i, (x i)^2)/(2*(v:ℝ))) * MvPolynomial.eval x P)) volume := by
    convert he using 1
    funext x
    ring
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).mp hmul

#print axioms correspondencePolynomial_realGaussian_density_integrable
end
end GinibrePoincare
