module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberResolvent
public import GinibrePoincare.Analysis.CorrespondenceOperatorCfcEigenvector
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem correspondenceOperatorNumberResolvent_basis (n : ℕ) (hn : 0<n)
    (pq : HermiteMultiIndex n) :
    correspondenceOperatorNumberResolvent n hn ((gaussianHermiteHilbertBasis n hn) pq)=
      correspondenceOperatorNumberResolventWeight n pq • (gaussianHermiteHilbertBasis n hn) pq := by
  classical
  apply gaussianHermiteCoefficient_ext hn
  intro ab
  rw [correspondenceOperatorNumberResolvent_coefficient]
  have hc (ij : HermiteMultiIndex n) :
      gaussianHermiteCoefficient hn ((gaussianHermiteHilbertBasis n hn) pq) ij=
        if ij=pq then 1 else 0 := by
    change (gaussianHermiteHilbertBasis n hn).repr ((gaussianHermiteHilbertBasis n hn) pq) ij=_
    rw [HilbertBasis.repr_self, lp.single_apply]
    simp [Pi.single_apply]
  have hsm : gaussianHermiteCoefficient hn
      (correspondenceOperatorNumberResolventWeight n pq • (gaussianHermiteHilbertBasis n hn) pq) ab=
      (correspondenceOperatorNumberResolventWeight n pq : ℂ)*
        gaussianHermiteCoefficient hn ((gaussianHermiteHilbertBasis n hn) pq) ab := by
    rw [gaussianHermiteCoefficient_eq_inner]
    change inner ℂ (multivariateNormalizedL2 n hn ab.1 ab.2)
      ((correspondenceOperatorNumberResolventWeight n pq : ℂ) • (gaussianHermiteHilbertBasis n hn) pq) = _
    rw [inner_smul_right,← gaussianHermiteCoefficient_eq_inner]
  rw [hsm, hc]
  by_cases h : ab=pq
  · subst ab
    simp [correspondenceOperatorNumberResolventWeight]
  · simp [h]

theorem correspondenceOperatorNumber_cfc_coefficient (n : ℕ) (hn : 0<n)
    (f : ℝ→ℝ) (hf : ContinuousOn f (spectrum ℝ (correspondenceOperatorNumberResolvent n hn)))
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (cfc f (correspondenceOperatorNumberResolvent n hn) u) pq=
      (f (correspondenceOperatorNumberResolventWeight n pq) : ℂ)*gaussianHermiteCoefficient hn u pq := by
  have hR := correspondenceOperatorNumberResolvent_isSelfAdjoint n hn
  have hx := correspondenceOperatorNumberResolvent_basis n hn pq
  have hr := correspondenceOperator_eigenvalue_mem_spectrum _ _ _
    ((gaussianHermiteHilbertBasis n hn).orthonormal.ne_zero pq) hx
  have he := correspondenceOperator_cfc_eigenvector _ hR _ hr _ hx f hf
  have hS := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (IsSelfAdjoint.cfc (f:=f) (a:=correspondenceOperatorNumberResolvent n hn)))
  rw [gaussianHermiteCoefficient_eq_inner,← gaussianHermiteHilbertBasis_apply]
  have hSym := hS ((gaussianHermiteHilbertBasis n hn) pq) u
  change inner ℂ (cfc f (correspondenceOperatorNumberResolvent n hn) ((gaussianHermiteHilbertBasis n hn) pq)) u=
    inner ℂ ((gaussianHermiteHilbertBasis n hn) pq) (cfc f (correspondenceOperatorNumberResolvent n hn) u) at hSym
  rw [← hSym, he]
  change inner ℂ ((f (correspondenceOperatorNumberResolventWeight n pq) : ℂ) • (gaussianHermiteHilbertBasis n hn) pq) u=_
  rw [inner_smul_left]
  simp only [Complex.conj_ofReal]
  rw [gaussianHermiteCoefficient_eq_inner, gaussianHermiteHilbertBasis_apply]
#print axioms correspondenceOperatorNumberResolvent_basis
#print axioms correspondenceOperatorNumber_cfc_coefficient
end
end GinibrePoincare
