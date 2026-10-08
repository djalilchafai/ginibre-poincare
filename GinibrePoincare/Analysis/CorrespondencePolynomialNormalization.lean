module
public import GinibrePoincare.Analysis.KostlanProductLaw
public import Mathlib.Algebra.BigOperators.Intervals
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Exact Gaussian-reference partition constant in the introductory footnote. -/
theorem correspondencePolynomial_partition_constant {n : ℕ} (hn : 0<n) :
    (ginibreNormalizingMass n).toReal =
      (n.factorial : ℝ)*(∏i : Fin n,(i.val.factorial : ℝ))/(n : ℝ)^(n*(n-1)/2) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have h := ginibre_radial_expectation_transfer n hn (fun _ => 1) continuous_const
    (fun σ r => rfl) 1 (by intro r; norm_num)
  simp only [mul_one,integral_const,probReal_univ,one_smul] at h
  have hi : (∫z,kostlanWeight n z ∂complexGaussianMeasure n)=
      ∏i : Fin n,(i.val.factorial : ℝ)/(n : ℝ)^i.val := by
    unfold kostlanWeight complexGaussianMeasure complexGaussianProbability
    simp only [ProbabilityMeasure.toMeasure_pi]
    exact (integral_fintype_prod_eq_prod (fun (i : Fin n) (z : ℂ) => Complex.normSq z^i.val)
      (μ := fun _ => (complexCoordinateGaussianProbability n : Measure ℂ))).trans
      (Finset.prod_congr rfl (fun i _ => integral_normSq_pow_coordinate n i.val hn))
  rw [hi,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum] at h
  have hs : (∑i : Fin n,i.val)=n*(n-1)/2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => i)]
    exact Finset.sum_range_id n
  rw [hs] at h
  have hm : (ginibreNormalizingMass n).toReal≠0 := ENNReal.toReal_ne_zero.mpr
    ⟨(ginibreMassEvaluation n hn).1.ne',(ginibreMassEvaluation n hn).2.ne⟩
  have hnR : (n : ℝ)≠0 := by exact_mod_cast hn.ne'
  field_simp [hm,hnR] at h ⊢
  nlinarith

#print axioms correspondencePolynomial_partition_constant
end
end GinibrePoincare
