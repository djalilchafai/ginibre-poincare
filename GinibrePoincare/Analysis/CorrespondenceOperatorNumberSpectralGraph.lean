module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberFormDomain
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-- Maximal spectral graph transported through the genuine orthonormal Hermite
basis. Its eigenvalues are f(n|q|); no finite-polynomial domain restriction occurs. -/
def correspondenceOperatorNumberSpectralGraph (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)×Lp ℂ 2 (complexGaussianMeasure n)) where
  carrier := {p | ∀pq, gaussianHermiteCoefficient hn p.2 pq=
    (f (n*totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn p.1 pq}
  zero_mem' := by simp [gaussianHermiteCoefficient_eq_inner]
  add_mem' := by
    intro p q hp hq pq
    change gaussianHermiteCoefficient hn (p.2+q.2) pq=
      (f (n*totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn (p.1+q.1) pq
    simp only [gaussianHermiteCoefficient_eq_inner, inner_add_right] at *
    rw [hp pq, hq pq, mul_add]
  smul_mem' := by
    intro a p hp pq
    change gaussianHermiteCoefficient hn (a • p.2) pq=
      (f (n*totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn (a • p.1) pq
    simp only [gaussianHermiteCoefficient_eq_inner, inner_smul_right] at *
    rw [hp pq]
    ring

theorem correspondenceOperatorNumberSpectralGraph_singleValued (n : ℕ) (hn : 0<n) (f : ℝ→ℝ)
    (p : Lp ℂ 2 (complexGaussianMeasure n)×Lp ℂ 2 (complexGaussianMeasure n))
    (hp : p∈correspondenceOperatorNumberSpectralGraph n hn f) (hx : p.1=0) : p.2=0 := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  simpa [hx, gaussianHermiteCoefficient_eq_inner] using hp pq

def correspondenceOperatorNumberSpectral (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) :
    Lp ℂ 2 (complexGaussianMeasure n)→ₗ.[ℂ]Lp ℂ 2 (complexGaussianMeasure n) :=
  (correspondenceOperatorNumberSpectralGraph n hn f).toLinearPMap

theorem correspondenceOperatorNumberSpectral_graph (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) :
    (correspondenceOperatorNumberSpectral n hn f).graph=correspondenceOperatorNumberSpectralGraph n hn f :=
  Submodule.toLinearPMap_graph_eq _ (correspondenceOperatorNumberSpectralGraph_singleValued n hn f)

theorem correspondenceOperatorNumberSpectral_domain_iff (n : ℕ) (hn : 0<n) (f : ℝ→ℝ)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∃v, (u, v)∈(correspondenceOperatorNumberSpectral n hn f).graph) ↔
      Summable (fun pq : HermiteMultiIndex n=>
        ‖(f (n*totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn u pq‖^2) := by
  rw [correspondenceOperatorNumberSpectral_graph]
  constructor
  · rintro ⟨v, hv⟩
    exact (hasSum_norm_sq_gaussianHermiteCoefficient hn v).summable.congr
      (fun pq=>by rw [hv pq])
  · intro hs
    let c : lp (fun _ : HermiteMultiIndex n=>ℂ) 2 :=
      ⟨fun pq=>(f (n*totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn u pq,
        memℓp_gen (by simpa using hs)⟩
    refine ⟨(gaussianHermiteHilbertBasis n hn).repr.symm c,?_⟩
    intro pq
    change ((gaussianHermiteHilbertBasis n hn).repr
      ((gaussianHermiteHilbertBasis n hn).repr.symm c)) pq=_
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- Literal maximal square-root graph domain equals the actual ordinary
Gaussian dbar form domain. Self-adjoint functional-calculus identification is
exported separately from this exact domain calculation. -/
theorem correspondenceOperatorNumber_sqrt_domain_iff_ordinary_form {n : ℕ} (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∃v, (u, v)∈(correspondenceOperatorNumberSpectral n hn Real.sqrt).graph) ↔
      ∃D : Fin n→Lp ℂ 2 (complexGaussianMeasure n),∀j, IsGaussianWeakDbar n u (D j) j := by
  rw [correspondenceOperatorNumberSpectral_domain_iff n hn Real.sqrt u,
    correspondenceOperatorNumber_ordinary_form_domain_iff hn u]
  have he (pq : HermiteMultiIndex n) :
      ‖(Real.sqrt (n*totalAntiDegree pq : ℕ) : ℂ)*gaussianHermiteCoefficient hn u pq‖^2=
        ((n*totalAntiDegree pq : ℕ) : ℝ)*‖gaussianHermiteCoefficient hn u pq‖^2 := by
    rw [norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _)]
  simp only [he]
#print axioms correspondenceOperatorNumberSpectral_domain_iff
#print axioms correspondenceOperatorNumber_sqrt_domain_iff_ordinary_form
end
end GinibrePoincare
