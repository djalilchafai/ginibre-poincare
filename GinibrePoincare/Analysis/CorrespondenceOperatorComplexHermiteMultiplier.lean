module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
public import GinibrePoincare.Analysis.GinibreFullSemigroupGenerator
@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
/-- Bounded complex spectral multipliers on the genuine Gaussian Hermite basis. -/
def correspondenceOperatorComplexHermiteMultiplierCoefficients {n : ℕ} (hn : 0<n)
    (w : HermiteMultiIndex n→ℂ) (hw : ∀pq,‖w pq‖≤1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) : lp (fun _ : HermiteMultiIndex n=>ℂ) 2 :=
  ⟨fun pq=>w pq*gaussianHermiteCoefficient hn u pq,
    (lp.memℓp ((gaussianHermiteHilbertBasis n hn).repr u)).mono' (by
      intro pq
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw pq))⟩

def correspondenceOperatorComplexHermiteMultiplierValue {n : ℕ} (hn : 0<n)
    (w : HermiteMultiIndex n→ℂ) (hw : ∀pq,‖w pq‖≤1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) : Lp ℂ 2 (complexGaussianMeasure n) :=
  (gaussianHermiteHilbertBasis n hn).repr.symm
    (correspondenceOperatorComplexHermiteMultiplierCoefficients hn w hw u)

@[simp] theorem correspondenceOperatorComplexHermiteMultiplier_coefficient {n : ℕ} (hn : 0<n)
    (w : HermiteMultiIndex n→ℂ) (hw : ∀pq,‖w pq‖≤1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (correspondenceOperatorComplexHermiteMultiplierValue hn w hw u) pq=
      w pq*gaussianHermiteCoefficient hn u pq := by
  simp [gaussianHermiteCoefficient,correspondenceOperatorComplexHermiteMultiplierValue,
    correspondenceOperatorComplexHermiteMultiplierCoefficients]

theorem correspondenceOperatorComplexHermiteMultiplier_norm_le {n : ℕ} (hn : 0<n)
    (w : HermiteMultiIndex n→ℂ) (hw : ∀pq,‖w pq‖≤1)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖correspondenceOperatorComplexHermiteMultiplierValue hn w hw u‖≤‖u‖ := by
  rw [correspondenceOperatorComplexHermiteMultiplierValue,LinearIsometryEquiv.norm_map,
    ← (gaussianHermiteHilbertBasis n hn).repr.norm_map u]
  apply lp.norm_mono (by norm_num)
  intro pq
  change ‖w pq*gaussianHermiteCoefficient hn u pq‖≤‖gaussianHermiteCoefficient hn u pq‖
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (hw pq)

def correspondenceOperatorComplexHermiteMultiplier {n : ℕ} (hn : 0<n)
    (w : HermiteMultiIndex n→ℂ) (hw : ∀pq,‖w pq‖≤1) :
    Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n) :=
  LinearMap.mkContinuous
    { toFun := correspondenceOperatorComplexHermiteMultiplierValue hn w hw
      map_add' := by
        intro u v
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (x y : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (x+y) pq =
              gaussianHermiteCoefficient hn x pq+gaussianHermiteCoefficient hn y pq := by
          simp only [gaussianHermiteCoefficient_eq_inner,inner_add_right]
        rw [correspondenceOperatorComplexHermiteMultiplier_coefficient,ha,ha,
          correspondenceOperatorComplexHermiteMultiplier_coefficient,
          correspondenceOperatorComplexHermiteMultiplier_coefficient,mul_add]
      map_smul' := by
        intro a u
        apply gaussianHermiteCoefficient_ext hn
        intro pq
        have ha (x : Lp ℂ 2 (complexGaussianMeasure n)) :
            gaussianHermiteCoefficient hn (a • x) pq =a*gaussianHermiteCoefficient hn x pq := by
          simp only [gaussianHermiteCoefficient_eq_inner,inner_smul_right]
        change gaussianHermiteCoefficient hn (correspondenceOperatorComplexHermiteMultiplierValue hn w hw (a • u)) pq =
          gaussianHermiteCoefficient hn (a • correspondenceOperatorComplexHermiteMultiplierValue hn w hw u) pq
        rw [correspondenceOperatorComplexHermiteMultiplier_coefficient,ha,ha,
          correspondenceOperatorComplexHermiteMultiplier_coefficient]
        ring }
    1 (by intro u; simpa using correspondenceOperatorComplexHermiteMultiplier_norm_le hn w hw u)


#print axioms correspondenceOperatorComplexHermiteMultiplier_coefficient
end
end GinibrePoincare
