module
public import GinibrePoincare.Analysis.AlternativeSpectralNumberPolynomial
public import GinibrePoincare.Analysis.HermiteInverseSquareRoot
public import Mathlib.Topology.Algebra.Module.LinearPMap
@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
/-- The maximal Hermite number graph, with the paper's eigenvalues n|q|. -/
def correspondenceOperatorNumberGraph (n : ℕ) (hn : 0<n) :
    Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n)) where
  carrier := {p | ∀pq, gaussianHermiteCoefficient hn p.2 pq =
    (n*totalAntiDegree pq:ℕ)*gaussianHermiteCoefficient hn p.1 pq}
  zero_mem' := by simp [gaussianHermiteCoefficient_eq_inner]
  add_mem' := by
    intro p q hp hq pq
    simp only [Prod.fst_add,Prod.snd_add,gaussianHermiteCoefficient_eq_inner,inner_add_right] at *
    rw [hp pq,hq pq,mul_add]
  smul_mem' := by
    intro a p hp pq
    change gaussianHermiteCoefficient hn (a • p.2) pq =
      (n*totalAntiDegree pq:ℕ)*gaussianHermiteCoefficient hn (a • p.1) pq
    simp only [gaussianHermiteCoefficient_eq_inner,inner_smul_right] at *
    rw [hp pq]
    ring

theorem correspondenceOperatorNumberGraph_singleValued (n : ℕ) (hn : 0<n)
    (p : Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))
    (hp : p∈correspondenceOperatorNumberGraph n hn) (hx : p.1=0) : p.2=0 := by
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  simpa [hx,gaussianHermiteCoefficient_eq_inner] using hp pq

/-- The genuine maximal unbounded number operator, rather than a compact-jet norm. -/
def correspondenceOperatorNumber (n : ℕ) (hn : 0<n) :
    Lp ℂ 2 (complexGaussianMeasure n) →ₗ.[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  (correspondenceOperatorNumberGraph n hn).toLinearPMap

theorem correspondenceOperatorNumber_graph (n : ℕ) (hn : 0<n) :
    (correspondenceOperatorNumber n hn).graph=correspondenceOperatorNumberGraph n hn :=
  Submodule.toLinearPMap_graph_eq _ (correspondenceOperatorNumberGraph_singleValued n hn)

/-- Exact maximal graph domain: the n|q| multiplier must be square summable. -/
theorem correspondenceOperatorNumber_domain_iff (n : ℕ) (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (∃v,(u,v)∈(correspondenceOperatorNumber n hn).graph) ↔
      Summable (fun pq : HermiteMultiIndex n =>
        ‖(n*totalAntiDegree pq:ℕ)*gaussianHermiteCoefficient hn u pq‖^2) := by
  rw [correspondenceOperatorNumber_graph]
  constructor
  · rintro ⟨v,hv⟩
    exact (hasSum_norm_sq_gaussianHermiteCoefficient hn v).summable.congr
      (fun pq=>by rw [hv pq])
  · intro hs
    let c : lp (fun _ : HermiteMultiIndex n=>ℂ) 2 :=
      ⟨fun pq=>(n*totalAntiDegree pq:ℕ)*gaussianHermiteCoefficient hn u pq,
        memℓp_gen (by simpa using hs)⟩
    refine ⟨(gaussianHermiteHilbertBasis n hn).repr.symm c,?_⟩
    intro pq
    change ((gaussianHermiteHilbertBasis n hn).repr
      ((gaussianHermiteHilbertBasis n hn).repr.symm c)) pq=_
    rw [LinearIsometryEquiv.apply_symm_apply]

/-- Literal finite differential number polynomials belong to the maximal graph. -/
theorem correspondenceOperatorNumber_finite_graph (n : ℕ) (hn : 0<n)
    (c : HermiteMultiIndex n→₀ℂ) :
    (finiteHermiteCombination n hn c,finiteGaussianNumberL2 n hn c)∈
      (correspondenceOperatorNumber n hn).graph := by
  rw [correspondenceOperatorNumber_graph]
  intro pq
  simp [finiteGaussianNumberL2,spectralNumberCoefficients,
    gaussianHermiteCoefficient_finiteHermiteCombination]

/-- The maximal number graph is closed in the literal value/operator L² topology. -/
theorem correspondenceOperatorNumberGraph_isClosed (n : ℕ) (hn : 0<n) :
    IsClosed (correspondenceOperatorNumberGraph n hn : Set
      (Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n))) := by
  change IsClosed {p : Lp ℂ 2 (complexGaussianMeasure n) × Lp ℂ 2 (complexGaussianMeasure n) | ∀pq, gaussianHermiteCoefficient hn p.2 pq =
    (n*totalAntiDegree pq:ℕ)*gaussianHermiteCoefficient hn p.1 pq}
  simp only [Set.ofPred_forall]
  apply isClosed_iInter
  intro pq
  simp only [gaussianHermiteCoefficient_eq_inner]
  exact isClosed_eq (continuous_const.inner continuous_snd)
    (continuous_const.mul (continuous_const.inner continuous_fst))

/-- Finite Hermite number polynomials approximate every maximal graph vector,
simultaneously in the genuine value and number-operator norms. -/
theorem correspondenceOperatorNumber_finite_core (n : ℕ) (hn : 0<n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u,v)∈(correspondenceOperatorNumber n hn).graph) :
    Tendsto (fun s=>finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn u s))
      atTop (𝓝 u) ∧
    Tendsto (fun s=>finiteGaussianNumberL2 n hn (gaussianHermiteFiniteCoefficients hn u s))
      atTop (𝓝 v) := by
  classical
  rw [correspondenceOperatorNumber_graph] at huv
  have hlim (x : Lp ℂ 2 (complexGaussianMeasure n)) :
      Tendsto (fun s=>finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn x s))
        atTop (𝓝 x) := by
    simp only [gaussianHermiteFiniteCoefficients_value]
    change HasSum (fun pq=>gaussianHermiteCoefficient hn x pq •
      (gaussianHermiteHilbertBasis n hn) pq) x
    simpa only [gaussianHermiteCoefficient] using (gaussianHermiteHilbertBasis n hn).hasSum_repr x
  refine ⟨hlim u,?_⟩
  have he (s : Finset (HermiteMultiIndex n)) :
      finiteGaussianNumberL2 n hn (gaussianHermiteFiniteCoefficients hn u s)=
        finiteHermiteCombination n hn (gaussianHermiteFiniteCoefficients hn v s) := by
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    simp only [finiteGaussianNumberL2,gaussianHermiteCoefficient_finiteHermiteCombination,
      spectralNumberCoefficients,spectralDiagonalCoefficients_apply]
    change (n*totalAntiDegree pq:ℕ)*((s:Set _).indicator (gaussianHermiteCoefficient hn u) pq)=
      (s:Set _).indicator (gaussianHermiteCoefficient hn v) pq
    by_cases hp : pq∈s
    · simp only [Finset.mem_coe,Set.indicator_of_mem hp]
      exact (huv pq).symm
    · simp [hp]
  simpa only [he] using hlim v
#print axioms correspondenceOperatorNumber_domain_iff
#print axioms correspondenceOperatorNumber_finite_graph
#print axioms correspondenceOperatorNumberGraph_isClosed
#print axioms correspondenceOperatorNumber_finite_core
end
end GinibrePoincare
