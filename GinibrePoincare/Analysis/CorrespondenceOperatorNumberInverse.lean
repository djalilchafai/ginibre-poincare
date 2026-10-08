module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberBochnerClosure
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberKernel
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
def correspondenceOperatorNumberInverse (n : ℕ) (hn : 0<n) :
    Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteInverseSquareRootCLM hn).comp (gaussianHermiteInverseSquareRootCLM hn)

/-- The actual bounded inverse sends every Gaussian L² input to the maximal
number domain and inverts its literal holomorphic orthogonal projection. -/
theorem correspondenceOperatorNumber_inverse_graph (n : ℕ) (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (correspondenceOperatorNumberInverse n hn u,u-gaussianHermiteMode hn 0 u)∈
      (correspondenceOperatorNumber n hn).graph := by
  rw [correspondenceOperatorNumber_graph]
  intro pq
  have hc : gaussianHermiteCoefficient hn (u-gaussianHermiteMode hn 0 u) pq=
      gaussianHermiteCoefficient hn u pq-
        (if totalAntiDegree pq=0 then gaussianHermiteCoefficient hn u pq else 0) := by
    rw [gaussianHermiteCoefficient_eq_inner,inner_sub_right,inner_basis_gaussianHermiteMode,
      ← gaussianHermiteCoefficient_eq_inner]
  rw [hc]
  change _=(n*totalAntiDegree pq:ℕ)*gaussianHermiteCoefficient hn
    (gaussianHermiteInverseSquareRoot hn (gaussianHermiteInverseSquareRoot hn u)) pq
  rw [gaussianHermiteCoefficient_inverseSquareRoot,gaussianHermiteCoefficient_inverseSquareRoot]
  by_cases hd : totalAntiDegree pq=0
  · simp [hd]
  · rw [if_neg hd,sub_zero]
    have hw : (hermiteInverseSquareRootWeight n (totalAntiDegree pq):ℂ)^2=
        ((n*totalAntiDegree pq:ℕ):ℂ)⁻¹ := by
      have hh := congrArg (fun x : ℝ=>(x:ℂ)) (hermiteInverseSquareRootWeight_sq hn (Nat.pos_of_ne_zero hd))
      simpa using hh
    have hk : ((n*totalAntiDegree pq:ℕ):ℂ)≠0 := by exact_mod_cast Nat.mul_ne_zero hn.ne' hd
    calc
      _ = (((n*totalAntiDegree pq:ℕ):ℂ)*(hermiteInverseSquareRootWeight n (totalAntiDegree pq):ℂ)^2)*
          gaussianHermiteCoefficient hn u pq := by rw [hw,mul_inv_cancel₀ hk,one_mul]
      _ = _ := by ring

/-- The genuine full-domain number operator is bounded below by n on the
literal holomorphic orthogonal complement. -/
theorem correspondenceOperatorNumber_gap {n : ℕ} (hn : 0<n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u,v)∈(correspondenceOperatorNumber n hn).graph)
    (hu0 : gaussianHermiteMode hn 0 u=0) : (n:ℝ)*‖u‖≤‖v‖ := by
  obtain ⟨D,Q,hD,hQ,hBK⟩ := correspondenceOperatorNumber_full_bochner_kodaira hn u v huv
  have hgap := gaussianWeakDbar_gap hn u D hD
  rw [hu0,norm_zero,zero_pow (by decide : 2≠0),sub_zero] at hgap
  have hnn : 0<(n:ℝ) := by exact_mod_cast hn
  have hfirst : (n:ℝ)*‖u‖^2≤∑j : Fin n,‖D j‖^2 := by
    field_simp at hgap
    simpa only [mul_comm] using hgap
  have hp : 0≤∑j : Fin n,∑k : Fin n,‖Q j k‖^2 :=
    Finset.sum_nonneg (fun j _=>Finset.sum_nonneg (fun k _=>sq_nonneg _))
  apply (sq_le_sq₀ (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
  nlinarith [mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg n)]

/-- The inverse on the literal holomorphic complement has the sharp norm bound. -/
theorem correspondenceOperatorNumber_inverse_complement (n : ℕ) (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : gaussianHermiteMode hn 0 u=0) :
    (correspondenceOperatorNumberInverse n hn u,u)∈(correspondenceOperatorNumber n hn).graph ∧
      gaussianHermiteMode hn 0 (correspondenceOperatorNumberInverse n hn u)=0 ∧
      ‖correspondenceOperatorNumberInverse n hn u‖≤(n:ℝ)⁻¹*‖u‖ := by
  have hg := correspondenceOperatorNumber_inverse_graph n hn u
  rw [hu,sub_zero] at hg
  have hm : gaussianHermiteMode hn 0 (correspondenceOperatorNumberInverse n hn u)=0 :=
    gaussianHermiteMode_zero_inverseSquareRoot hn _
  refine ⟨hg,hm,?_⟩
  have hgap := correspondenceOperatorNumber_gap hn _ u hg hm
  have hnR : 0<(n:ℝ) := by exact_mod_cast hn
  have h := mul_le_mul_of_nonneg_left hgap (inv_nonneg.mpr hnR.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hnR.ne',one_mul] using h
#print axioms correspondenceOperatorNumber_inverse_graph
#print axioms correspondenceOperatorNumber_gap
#print axioms correspondenceOperatorNumber_inverse_complement
end
end GinibrePoincare
