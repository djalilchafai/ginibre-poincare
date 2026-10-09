module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
public import GinibrePoincare.Analysis.AlternativeBochnerKodairaPolynomial
@[expose] public section
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
def correspondenceOperatorFiniteSecond (n : ℕ) (hn : 0<n) (j k : Fin n) :
    (HermiteMultiIndex n→₀ℂ)→ₗ[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  (Finsupp.linearCombination ℂ (hermiteL2Family n hn)).comp
    ((spectralLoweringCoefficients n k).comp (spectralLoweringCoefficients n j))
theorem correspondenceOperatorFiniteSecond_eq (n : ℕ) (hn : 0<n)
    (j k : Fin n) (c : HermiteMultiIndex n→₀ℂ) :
    correspondenceOperatorFiniteSecond n hn j k c=
      finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) k) := by
  simp [correspondenceOperatorFiniteSecond, spectralLoweringCoefficients_eq, finiteHermiteCombination]

def correspondenceOperatorFiniteNumber (n : ℕ) (hn : 0<n) :
    (HermiteMultiIndex n→₀ℂ)→ₗ[ℂ] Lp ℂ 2 (complexGaussianMeasure n) :=
  (Finsupp.linearCombination ℂ (hermiteL2Family n hn)).comp (spectralNumberCoefficients n)

theorem correspondenceOperatorFiniteSecond_norm_le (n : ℕ) (hn : 0<n)
    (j k : Fin n) (c : HermiteMultiIndex n→₀ℂ) :
    ‖correspondenceOperatorFiniteSecond n hn j k c‖≤‖finiteGaussianNumberL2 n hn c‖ := by
  rw [correspondenceOperatorFiniteSecond_eq]
  have hBK := bkFinite_integrated_identity n hn c
  have h1 : ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) k)‖^2≤
      ∑l : Fin n, ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) l)‖^2 :=
    Finset.single_le_sum (fun l _=>sq_nonneg ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) l)‖) (Finset.mem_univ k)
  have h2 : (∑l : Fin n, ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c j) l)‖^2)≤
      ∑i : Fin n,∑l : Fin n, ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c i) l)‖^2 :=
    Finset.single_le_sum (fun i _=>Finset.sum_nonneg (s := Finset.univ) (fun l _=>
      sq_nonneg ‖finiteHermiteCombination n hn (loweredCoefficients n (loweredCoefficients n c i) l)‖)) (Finset.mem_univ j)
  have hp : 0≤(n : ℝ)*(∑j : Fin n, ‖finiteDbarComponentL2 n hn c j‖^2) :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun j _=>sq_nonneg _))
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  linarith

theorem correspondenceOperatorFiniteSecond_dist_le (n : ℕ) (hn : 0<n)
    (j k : Fin n) (c d : HermiteMultiIndex n→₀ℂ) :
    dist (correspondenceOperatorFiniteSecond n hn j k c) (correspondenceOperatorFiniteSecond n hn j k d)≤
      dist (finiteGaussianNumberL2 n hn c) (finiteGaussianNumberL2 n hn d) := by
  rw [dist_eq_norm, dist_eq_norm,← map_sub]
  have he : finiteGaussianNumberL2 n hn c-finiteGaussianNumberL2 n hn d=
      finiteGaussianNumberL2 n hn (c-d) := by
    change correspondenceOperatorFiniteNumber n hn c-correspondenceOperatorFiniteNumber n hn d=
      correspondenceOperatorFiniteNumber n hn (c-d)
    rw [map_sub]
  rw [he]
  exact correspondenceOperatorFiniteSecond_norm_le n hn j k (c-d)
#print axioms correspondenceOperatorFiniteSecond_norm_le
#print axioms correspondenceOperatorFiniteSecond_dist_le
end
end GinibrePoincare
