module
public import GinibrePoincare.Analysis.CorrespondenceGUECenterIntegrals
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueCenterVariance (n : ℕ) : ℝ≥0 := ⟨(n : ℝ)⁻¹, inv_nonneg.mpr (Nat.cast_nonneg n)⟩

theorem gueCenterVariance_ne_zero {n : ℕ} (hn : 0<n) : gueCenterVariance n≠0 := by
  change (⟨(n : ℝ)⁻¹, _⟩ : ℝ≥0)≠0
  intro hz
  have h : (n : ℝ)⁻¹=0 := congrArg (fun v : ℝ≥0 => (v : ℝ)) hz
  exact inv_ne_zero (by exact_mod_cast hn.ne' : (n : ℝ)≠0) h

theorem gueCenterGaussian_pdf (n : ℕ) (hn : 0<n) (t : ℝ) :
    gaussianPDFReal 0 (gueCenterVariance n) t=
      gaussianPDFReal 0 (gueCenterVariance n) 0*Real.exp (-(n : ℝ)/2*t^2) := by
  change (Real.sqrt (2*Real.pi*(n : ℝ)⁻¹))⁻¹*Real.exp (-(t-0)^2/(2*(n : ℝ)⁻¹))=
    ((Real.sqrt (2*Real.pi*(n : ℝ)⁻¹))⁻¹*Real.exp (-(0-0)^2/(2*(n : ℝ)⁻¹)))*Real.exp (-(n : ℝ)/2*t^2)
  simp only [sub_zero, zero_sub, neg_zero, zero_pow (by decide : 2≠0), zero_div,
    Real.exp_zero, mul_one]
  congr 1
  congr 1
  field_simp

theorem gueFullMeasure_center_gaussian_integral {n : ℕ} (hn : 0<n) (f : ℝ→ℝ) :
    (∫x, f (gueCenterCoordinate n x) ∂gueFullMeasure n)=
      (∫t, f t ∂gaussianReal 0 (gueCenterVariance n)) := by
  rw [gueFullMeasure_center_integral hn]
  have hpdf : gaussianPDFReal 0 (gueCenterVariance n)=fun t : ℝ =>
      gaussianPDFReal 0 (gueCenterVariance n) 0*Real.exp (-(n : ℝ)/2*t^2) :=
    funext (gueCenterGaussian_pdf n hn)
  have hg : (∫t, f t ∂gaussianReal 0 (gueCenterVariance n))=
      gaussianPDFReal 0 (gueCenterVariance n) 0*(∫t, Real.exp (-(n : ℝ)/2*t^2)*f t) := by
    rw [integral_gaussianReal_eq_integral_smul (gueCenterVariance_ne_zero hn)]
    rw [hpdf]
    simp only [smul_eq_mul, mul_assoc]
    rw [integral_const_mul]
    simp
  have hp : gaussianPDFReal 0 (gueCenterVariance n) 0*(∫t : ℝ, Real.exp (-(n : ℝ)/2*t^2))=1 := by
    have h := integral_gaussianPDFReal_eq_one 0 (gueCenterVariance_ne_zero hn)
    rw [hpdf] at h
    rw [integral_const_mul] at h
    exact h
  rw [hg]
  have hz : (∫t : ℝ, Real.exp (-(n : ℝ)/2*t^2))≠0 := by
    intro h
    rw [h, mul_zero] at hp
    norm_num at hp
  apply (div_eq_iff hz).mpr
  rw [mul_assoc, mul_left_comm, hp, mul_one]


theorem gueCenterCoordinate_measurePreserving {n : ℕ} (hn : 0<n) :
    MeasurePreserving (gueCenterCoordinate n) (gueFullMeasure n) (gaussianReal 0 (gueCenterVariance n)) := by
  letI := gueFullMeasure_probability hn
  have hm : Measurable (gueCenterCoordinate n) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n)).measurable
  refine ⟨hm, Measure.ext (fun s hs => ?_)⟩
  have hi := gueFullMeasure_center_gaussian_integral hn (s.indicator (fun _ => 1))
  rw [← integral_map hm.aemeasurable (by exact (measurable_const.indicator hs).aestronglyMeasurable)] at hi
  change (∫t, s.indicator (1 : ℝ→ℝ) t ∂(gueFullMeasure n).map (gueCenterCoordinate n))=
    (∫t, s.indicator (1 : ℝ→ℝ) t ∂gaussianReal 0 (gueCenterVariance n)) at hi
  rw [integral_indicator_one hs, integral_indicator_one hs] at hi
  calc
    (gueFullMeasure n).map (gueCenterCoordinate n) s =
        ENNReal.ofReal (((gueFullMeasure n).map (gueCenterCoordinate n) s).toReal) :=
      (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
    _ = ENNReal.ofReal ((gaussianReal 0 (gueCenterVariance n) s).toReal) := congrArg ENNReal.ofReal hi
    _ = gaussianReal 0 (gueCenterVariance n) s := ENNReal.ofReal_toReal (measure_lt_top _ _).ne

#print axioms gueCenterCoordinate_measurePreserving

#print axioms gueFullMeasure_center_gaussian_integral
end
end GinibrePoincare
