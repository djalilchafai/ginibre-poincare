module
public import GinibrePoincare.Analysis.AlternativeSlaterLowering
public import GinibrePoincare.Analysis.AlternativeSpectralNumberPolynomial
public import GinibrePoincare.Analysis.L2RepresentativeBridges
public import GinibrePoincare.Analysis.GaussianDbarCompactCore
public import GinibrePoincare.Analysis.GinibreRadialGamma
public import GinibrePoincare.Analysis.GlobalPhaseAction
public import GinibrePoincare.Analysis.NonQuadraticHomogeneousPolynomial
public import Mathlib.Analysis.Analytic.Polynomial
@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
open ComplexHermite
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def slaterFiniteCoefficients {n : ℕ} (pq : HermiteMultiIndex n) : HermiteMultiIndex n →₀ ℂ :=
  (Real.sqrt (slaterMultiplicity n) : ℂ)⁻¹ •
    ∑ σ : ParticlePermutation n, permutationSign σ • Finsupp.single (slaterPermutedIndex σ pq) 1

theorem slaterFiniteCoefficients_function {n : ℕ} (hn : 0 < n) (pq : HermiteMultiIndex n) :
    finiteHermiteFunction n hn (slaterFiniteCoefficients pq) = slaterDeterminant hn pq := by
  funext z
  rw [slaterDeterminant_signed_tensor_sum]
  simp [finiteHermiteFunction,slaterFiniteCoefficients,map_sum,Finsupp.linearCombination_single,
    smul_apply,smul_eq_mul]

theorem slaterFiniteCoefficients_number {n : ℕ} (pq : HermiteMultiIndex n) :
    spectralNumberCoefficients n (slaterFiniteCoefficients pq) =
      (n*totalAntiDegree pq : ℕ) • slaterFiniteCoefficients pq := by
  classical
  have hm (σ : ParticlePermutation n) : spectralNumberCoefficients n
      (permutationSign σ • Finsupp.single (slaterPermutedIndex σ pq) 1) =
      (n*totalAntiDegree pq : ℕ) • (permutationSign σ • Finsupp.single (slaterPermutedIndex σ pq) 1) := by
    simp only [spectralNumberCoefficients,map_smul,spectralDiagonalCoefficients,
      Finsupp.linearCombination_single]
    rw [slaterPermutedIndex_totalAntiDegree]
    simp [smul_smul,mul_comm]
  unfold slaterFiniteCoefficients
  rw [map_smul,map_sum]
  simp_rw [hm]
  rw [← Finset.smul_sum,smul_comm]

/-- Literal Section 4 (4.2) on every point, including repeated orbital labels. -/
theorem slaterDeterminant_number_eigenfunction {n : ℕ} (hn : 0 < n)
    (pq : HermiteMultiIndex n) (z : Configuration n) :
    (∑ j : Fin n, gaussianDbarAdjointTest j (dbarComponent (slaterDeterminant hn pq) j) z) =
      (n*totalAntiDegree pq : ℕ) * slaterDeterminant hn pq z := by
  have ha := finiteGaussianNumberL2_ae n hn (slaterFiniteCoefficients pq)
  have hb := finiteHermiteCombination_coeFn n hn
    (spectralNumberCoefficients n (slaterFiniteCoefficients pq))
  have hc : (fun z => (n*totalAntiDegree pq : ℕ)*slaterDeterminant hn pq z) =ᵐ[complexGaussianMeasure n]
      (fun z => ∑ j : Fin n,gaussianDbarAdjointTest j (dbarComponent (slaterDeterminant hn pq) j) z) := by
    filter_upwards [ha,hb] with z hza hzb
    unfold finiteGaussianNumberL2 at hza
    rw [hzb,slaterFiniteCoefficients_function] at hza
    rw [slaterFiniteCoefficients_number] at hza
    change finiteHermiteFunction n hn ((n*totalAntiDegree pq : ℕ) • slaterFiniteCoefficients pq) z = _ at hza
    have he : finiteHermiteFunction n hn ((n*totalAntiDegree pq : ℕ) • slaterFiniteCoefficients pq) =
        (n*totalAntiDegree pq : ℕ) • finiteHermiteFunction n hn (slaterFiniteCoefficients pq) := by
      exact map_nsmul (Finsupp.linearCombination ℂ _) _ _
    rw [he,slaterFiniteCoefficients_function] at hza
    simpa [smul_apply,nsmul_eq_mul] using hza
  have hs : ContDiff ℝ ∞ (slaterDeterminant hn pq) := by
    rw [← slaterFiniteCoefficients_function hn pq]
    exact contDiff_finiteHermiteFunction_smooth n hn _
  have he := continuous_eq_of_ae_eq_complexGaussian hn (contDiff_const.mul hs).continuous
    (continuous_finsetSum _ (fun j hj => (bkAdjoint_contDiff (bkDbar_contDiff hs j) j).continuous)) hc
  exact (congrFun he z).symm


theorem slaterHolomorphicPolynomial_homogeneous (n : ℕ) (p : Fin n → ℕ) :
    (slaterHolomorphicPolynomial n p).IsHomogeneous (∑ i,p i) := by
  unfold slaterHolomorphicPolynomial
  apply MvPolynomial.IsHomogeneous.C_mul
  rw [Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro σ hσ
  apply MvPolynomial.IsHomogeneous.C_mul
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin n => MvPolynomial.C (oneDimNormalization n (p (σ i)) : ℂ)*
      MvPolynomial.X i ^ p (σ i))
    (fun i => p (σ i)) (fun i hi =>
      (MvPolynomial.isHomogeneous_X_pow i (p (σ i))).C_mul _)
  simpa only [Equiv.sum_comp σ p] using h

theorem slaterHolomorphicPolynomial_ne_zero {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p) : slaterHolomorphicPolynomial n p ≠ 0 := by
  intro hz
  have hdist : SlaterDistinct (p,0) := by
    intro i j hij
    exact hp (congrArg Prod.fst hij)
  have he : slaterL2 hn (p,0) = 0 := by
    apply Lp.ext
    filter_upwards [slaterL2_ae hn (p,0),Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hs h0
    rw [hs,h0,←eval_slaterHolomorphicPolynomial hn,hz]
    simp
  have hnorm := slaterL2_norm_eq_one hn (p,0) hdist
  rw [he,norm_zero] at hnorm
  norm_num at hnorm

/-- Literal polynomial homogeneity of the quotient, with the exact degree
`sum a - n(n-1)/2` asserted in Section 4 (4.6). -/
theorem slater_zero_degree_homogeneous_quotient {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p) :
    ∃ Q : ConfigurationPolynomial n, IsSymmetricConfigurationPolynomial Q ∧
      (∀ z,slaterDeterminant hn (p,0) z = vandermonde z*MvPolynomial.eval z Q) ∧
      Q.IsHomogeneous ((∑ i,p i)-vandermondeDegree n) ∧
      vandermondeDegree n ≤ ∑ i,p i ∧
      2*vandermondeDegree n = n*(n-1) := by
  obtain ⟨Q,hQ,hfac,hle,hscale⟩ := homogeneous_alternating_polynomial_division
    (slaterHolomorphicPolynomial_homogeneous n p)
    (slaterHolomorphicPolynomial_alternating n hn p) (slaterHolomorphicPolynomial_ne_zero hn p hp)
  have hphase : ∀ (u : ℂ) (z : Configuration n), ‖u‖=1 →
      MvPolynomial.eval (u • z) Q = u^((∑ i,p i)-vandermondeDegree n)*MvPolynomial.eval z Q := by
    intro u z hu
    have ha : (fun z : Configuration n => MvPolynomial.eval (u • z) Q) =ᵐ[complexGaussianMeasure n]
        (fun z => u^((∑ i,p i)-vandermondeDegree n)*MvPolynomial.eval z Q) := by
      filter_upwards [vandermondeDensity_ne_zero_ae n] with z hz
      apply hscale u hu z
      intro hv
      exact hz (by simp [vandermondeDensity,vandermondeWeight,hv])
    have hc1 : Continuous (fun z : Configuration n => MvPolynomial.eval (u • z) Q) :=
      (MvPolynomial.continuous_eval Q).comp (continuous_id.const_smul u)
    have hc2 : Continuous (fun z : Configuration n =>
        u^((∑ i,p i)-vandermondeDegree n)*MvPolynomial.eval z Q) :=
      continuous_const.mul (MvPolynomial.continuous_eval Q)
    have he : (fun z : Configuration n => MvPolynomial.eval (u • z) Q) =
        (fun z => u^((∑ i,p i)-vandermondeDegree n)*MvPolynomial.eval z Q) :=
      continuous_eq_of_ae_eq_complexGaussian hn hc1 hc2 ha
    exact congrFun he z
  have hA := AnalyticOnNhd.eval_mvPolynomial Q
  obtain ⟨R,hR,hEval⟩ := entire_phase_has_homogeneous_mvPolynomial
    (fun z : Configuration n => MvPolynomial.eval z Q)
    (fun z => (hA z (Set.mem_univ z)).differentiableAt)
    (hA 0 (Set.mem_univ 0)) hphase
  have hQR : Q=R := by
    apply MvPolynomial.funext
    exact hEval
  refine ⟨Q,hQ,?_,hQR.symm ▸ hR,hle,vandermondeDegree_twice n⟩
  intro z
  rw [←eval_slaterHolomorphicPolynomial hn,hfac,map_mul,eval_polynomialVandermonde]


/-- The numerical degree formula exactly as written in (4.6). -/
theorem slater_zero_degree_homogeneous_quotient_exact {n : ℕ} (hn : 0 < n)
    (p : Fin n → ℕ) (hp : Function.Injective p) :
    ∃ Q : ConfigurationPolynomial n, IsSymmetricConfigurationPolynomial Q ∧
      (∀ z,slaterDeterminant hn (p,0) z = vandermonde z*MvPolynomial.eval z Q) ∧
      Q.IsHomogeneous ((∑ i,p i)-n*(n-1)/2) := by
  obtain ⟨Q,hQ,hfac,hhom,hle,hdegree⟩ := slater_zero_degree_homogeneous_quotient hn p hp
  have hd : vandermondeDegree n = n*(n-1)/2 := by omega
  exact ⟨Q,hQ,hfac,by simpa only [hd] using hhom⟩

#print axioms slaterFiniteCoefficients_function
#print axioms slaterFiniteCoefficients_number
#print axioms slaterDeterminant_number_eigenfunction
#print axioms slaterHolomorphicPolynomial_homogeneous
#print axioms slaterHolomorphicPolynomial_ne_zero
#print axioms slater_zero_degree_homogeneous_quotient
#print axioms slater_zero_degree_homogeneous_quotient_exact
end
end GinibrePoincare
