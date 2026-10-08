module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-- Every maximal number-domain vector has all literal distributional dbar
derivatives in Gaussian L²; the analytic domain fact is proved from its graph. -/
theorem correspondenceOperatorNumber_weak_dbar_exists {n : ℕ} (hn : 0<n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u,v)∈(correspondenceOperatorNumber n hn).graph) (j : Fin n) :
    ∃D,IsGaussianWeakDbar n u D j := by
  rw [correspondenceOperatorNumber_graph] at huv
  apply (gaussianWeakDbar_exists_iff_summable hn u j).mpr
  have hs := (hasSum_norm_sq_gaussianHermiteCoefficient hn v).summable.comp_injective
    (raiseHermiteIndex_injective j)
  apply Summable.of_nonneg_of_le (fun _=>sq_nonneg _) _ hs
  intro pq
  change ‖(Real.sqrt (n*(pq.2 j+1):ℕ):ℂ)*gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)‖^2 ≤
    ‖gaussianHermiteCoefficient hn v (raiseHermiteIndex j pq)‖^2
  rw [huv (raiseHermiteIndex j pq)]
  have hj : pq.2 j+1≤totalAntiDegree (raiseHermiteIndex j pq) := by
    have h := Finset.single_le_sum (fun i _=>Nat.zero_le ((raiseHermiteIndex j pq).2 i))
      (Finset.mem_univ j)
    simpa [raiseHermiteIndex,raiseAt,totalAntiDegree] using h
  have ha : (n*(pq.2 j+1):ℕ)≤n*totalAntiDegree (raiseHermiteIndex j pq) :=
    Nat.mul_le_mul_left n hj
  have hb : 1≤n*totalAntiDegree (raiseHermiteIndex j pq) :=
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne'
      (Nat.ne_of_gt (lt_of_lt_of_le (Nat.succ_pos _) hj))))
  have hsqrt : Real.sqrt (n*(pq.2 j+1):ℕ)≤(n*totalAntiDegree (raiseHermiteIndex j pq):ℕ) := by
    have hBR : (1:ℝ)≤(n*totalAntiDegree (raiseHermiteIndex j pq):ℕ) := by exact_mod_cast hb
    have hAR : ((n*(pq.2 j+1):ℕ):ℝ)≤(n*totalAntiDegree (raiseHermiteIndex j pq):ℕ) := by
      exact_mod_cast ha
    apply (Real.sqrt_le_iff).mpr
    constructor
    · positivity
    · nlinarith
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hnrm : ‖((n*totalAntiDegree (raiseHermiteIndex j pq):ℕ):ℂ)‖=
      ((n*totalAntiDegree (raiseHermiteIndex j pq):ℕ):ℝ) := by
    norm_cast
  rw [hnrm]
  exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg (gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)))) (mul_le_mul_of_nonneg_right hsqrt (norm_nonneg (gaussianHermiteCoefficient hn u (raiseHermiteIndex j pq)))) 2
#print axioms correspondenceOperatorNumber_weak_dbar_exists
end
end GinibrePoincare
