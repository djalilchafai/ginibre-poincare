module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberCompactGraph
public import GinibrePoincare.Analysis.AlternativeBochnerKodairaPolynomial
public import GinibrePoincare.Analysis.CorrespondencePolynomialGaussian
@[expose] public section
open MeasureTheory Filter
open scoped ContDiff ComplexConjugate BigOperators Topology
namespace GinibrePoincare
open ComplexHermite
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem correspondenceNumber_hermite_polynomial (n : ℕ) (hn : 0<n)
    (p q : Fin n→ℕ) : ∃P : GinibreMixedPolynomial n, ginibreMixedPolynomialEval P=multivariateNormalized n hn p q := by
  refine ⟨∏i : Fin n, MvPolynomial.C ((oneDimNormalization n (p i)*oneDimNormalization n (q i) : ℝ) : ℂ)*
    ∑k∈Finset.range (min (p i) (q i)+1),
      MvPolynomial.C (((-((n : ℝ)⁻¹ : ℂ))^k)*(k.factorial : ℂ)*(Nat.choose (p i) k : ℂ)*(Nat.choose (q i) k : ℂ))*
        MvPolynomial.X (i, 0)^(p i-k)*MvPolynomial.X (i, 1)^(q i-k),?_⟩
  funext z
  simp [ginibreMixedPolynomialEval, multivariateNormalized, normalizedEval_eq_sum]

theorem correspondenceNumber_finite_polynomial (n : ℕ) (hn : 0<n)
    (c : HermiteMultiIndex n→₀ℂ) : ∃P : GinibreMixedPolynomial n, ginibreMixedPolynomialEval P=finiteHermiteFunction n hn c := by
  classical
  choose P hP using fun pq : HermiteMultiIndex n=>correspondenceNumber_hermite_polynomial n hn pq.1 pq.2
  refine ⟨∑pq∈c.support, MvPolynomial.C (c pq)*P pq,?_⟩
  funext z
  simp only [ginibreMixedPolynomialEval, map_sum, map_mul, MvPolynomial.eval_C]
  change (∑pq∈c.support, c pq*ginibreMixedPolynomialEval (P pq) z)=_
  simp only [hP, finiteHermiteFunction, Finsupp.linearCombination_apply, Finsupp.sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

theorem correspondenceNumber_double_coordinate_memLp (n : ℕ) (hn : 0<n)
    (c : HermiteMultiIndex n→₀ℂ) (j k : Fin n) :
    MemLp (fun z =>z k*z j*finiteHermiteFunction n hn c z) 2 (complexGaussianMeasure n) := by
  obtain ⟨P, hP⟩ := correspondenceNumber_finite_polynomial n hn c
  have h := correspondencePolynomial_gaussian_memLp n (MvPolynomial.X (k, 0)*MvPolynomial.X (j, 0)*P)
  have he : ginibreMixedPolynomialEval (MvPolynomial.X (k, 0)*MvPolynomial.X (j, 0)*P)=
      (fun z=>z k*z j*finiteHermiteFunction n hn c z) := by
    funext z
    simp only [ginibreMixedPolynomialEval, map_mul, MvPolynomial.eval_X, ite_true]
    rw [← hP]
    rfl
  rwa [he] at h

theorem correspondenceNumber_secondCutoff_memLp {n : ℕ}
    (f : Configuration n→ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) (m : ℕ) :
    MemLp (fun z=>((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ)*f z)
      2 (complexGaussianMeasure n) := by
  obtain ⟨M, hM0, hM⟩ := bkCutoff_second_derivative_bound
  have hc : Continuous (deriv (deriv (sobolevCutoff m))) :=
    ((show ContDiff ℝ ((∞:ℕ∞ω)+1) (sobolevCutoff m) by simpa using sobolevCutoff_smooth m).deriv').continuous_deriv (by simp)
  apply hf.of_le_mul (c:=M) ((Complex.continuous_ofReal.comp (hc.comp contDiff_configurationNormSq.continuous)).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with z
  simp only [Pi.mul_apply, Function.comp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact (hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α:=ℝ) m; nlinarith))

theorem correspondenceNumber_secondCutoff_tendsto {n : ℕ}
    (f : Configuration n→ℂ) (hf : MemLp f 2 (complexGaussianMeasure n)) :
    Tendsto (fun m=>(correspondenceNumber_secondCutoff_memLp f hf m).toLp
      (fun z=>((deriv (deriv (sobolevCutoff m)) (configurationNormSq z) : ℝ) : ℂ)*f z)) atTop (𝓝 0) := by
  obtain ⟨M, hM0, hM⟩ := bkCutoff_second_derivative_bound
  have hz : MemLp (fun _ : Configuration n=>(0 : ℂ)) 2 (complexGaussianMeasure n) := MemLp.zero'
  have hi : Integrable (fun z=>(M*‖f z‖)^2) (complexGaussianMeasure n) := by
    simpa only [mul_pow] using ((memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf).const_mul (M^2)
  have ht := gaussianL2_toLp_tendsto_of_dominated_error _ _
    (correspondenceNumber_secondCutoff_memLp f hf) hz (fun z=>M*‖f z‖) hi
    (fun m z=>by
      rw [sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right ((hM m _).trans (div_le_self hM0 (by have := Nat.cast_nonneg (α:=ℝ) m; nlinarith))) (norm_nonneg _))
    (fun z=>by simpa using (Complex.continuous_ofReal.tendsto 0 |>.comp (bkCutoff_second_derivative_tendsto (configurationNormSq z))).mul_const (f z))
  simpa using ht

end
end GinibrePoincare
