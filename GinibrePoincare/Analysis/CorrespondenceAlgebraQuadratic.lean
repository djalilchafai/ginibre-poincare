module
public import GinibrePoincare.Analysis.PolynomialSectorIncompleteness
@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def correspondenceRelativePhase (n : ℕ) (ζ : ℂ) (z : Configuration n) : Configuration n :=
  fun j => coordinateSum z/(n : ℂ)+ζ*recenteredConfiguration n z j

theorem correspondenceRelativePhase_sum {n : ℕ} (hn : 0<n) (ζ : ℂ) (z : Configuration n) :
    coordinateSum (correspondenceRelativePhase n ζ z) = coordinateSum z := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [correspondenceRelativePhase,coordinateSum,Finset.sum_add_distrib,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,← Finset.mul_sum]
  change (n : ℂ)*(coordinateSum z/(n : ℂ))+ζ*coordinateSum (recenteredConfiguration n z) = coordinateSum z
  rw [coordinateSum_recentered,mul_zero,add_zero]
  exact mul_div_cancel₀ _ hnC

theorem correspondenceRelativePhase_recenter {n : ℕ} (hn : 0<n) (ζ : ℂ) (z : Configuration n) :
    recenteredConfiguration n (correspondenceRelativePhase n ζ z) =
      fun j => ζ*recenteredConfiguration n z j := by
  ext j
  simp only [recenteredConfiguration,projectToOrthogonal]
  rw [correspondenceRelativePhase_sum hn]
  simp only [correspondenceRelativePhase,recenteredConfiguration,projectToOrthogonal]
  ring

/-- Remark 1.6 covariance holds for every complex phase, hence every angle. -/
theorem correspondenceQuadratic_arbitrary_phase {n : ℕ} (hn : 0<n) (ζ : ℂ) (z : Configuration n) :
    ginibreCenteredQuadratic n (correspondenceRelativePhase n ζ z) = ζ^2*ginibreCenteredQuadratic n z := by
  unfold ginibreCenteredQuadratic
  rw [correspondenceRelativePhase_recenter hn]
  simp only [mul_pow,← Finset.mul_sum]

/-- Literal center/relative quadratic decomposition in Remark 1.6. -/
theorem correspondenceQuadratic_sum_decomposition {n : ℕ} (hn : 0<n) (z : Configuration n) :
    (∑ j, z j^2) = (coordinateSum z)^2/(n : ℂ)+ginibreCenteredQuadratic n z := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hp : ginibreCenteredQuadratic n z =
      (∑ j, z j^2)-2*(coordinateSum z/(n : ℂ))*coordinateSum z+
        (n : ℂ)*(coordinateSum z/(n : ℂ))^2 := by
    unfold ginibreCenteredQuadratic recenteredConfiguration projectToOrthogonal
    simp_rw [sub_sq]
    simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Finset.sum_mul]
    change _ = _
    simp only [coordinateSum,← Finset.mul_sum]
    ring
  rw [hp]
  field_simp
  ring

#print axioms correspondenceQuadratic_arbitrary_phase
#print axioms correspondenceQuadratic_sum_decomposition
end
end GinibrePoincare
