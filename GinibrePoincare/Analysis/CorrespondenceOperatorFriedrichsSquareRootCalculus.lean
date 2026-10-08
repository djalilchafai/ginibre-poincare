module
public import GinibrePoincare.Analysis.CorrespondenceOperatorFriedrichsSquareRootRange
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
@[expose] public section
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem correspondenceFriedrichs_one_sub_resolvent_nonneg (n : ℕ) (hn : 0<n) :
    0≤1-correspondenceOperatorComplexResolvent n hn := by
  apply ContinuousLinearMap.nonneg_iff_isPositive.mpr
  refine ⟨ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
    ((IsSelfAdjoint.one (GinibreFullComplexL2 n→L[ℂ]GinibreFullComplexL2 n)).sub (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)),?_⟩
  intro x
  have h1 := RCLike.re_le_norm (inner ℂ (correspondenceOperatorComplexResolvent n hn x) x)
  have h2 := norm_inner_le_norm (𝕜:=ℂ) (correspondenceOperatorComplexResolvent n hn x) x
  have h3 := correspondenceOperatorComplexResolvent_norm_le n hn x
  change 0≤RCLike.re (inner ℂ ((1-correspondenceOperatorComplexResolvent n hn) x) x)
  rw [sub_apply,one_apply_eq_self,inner_sub_left,map_sub,inner_self_eq_norm_sq]
  nlinarith [norm_nonneg x,norm_nonneg (correspondenceOperatorComplexResolvent n hn x)]

def correspondenceFriedrichsComplementSqrt (n : ℕ) (hn : 0<n) :
    GinibreFullComplexL2 n→L[ℂ]GinibreFullComplexL2 n :=
  CFC.sqrt (1-correspondenceOperatorComplexResolvent n hn)

theorem correspondenceFriedrichsComplementSqrt_square (n : ℕ) (hn : 0<n) :
    correspondenceFriedrichsComplementSqrt n hn*correspondenceFriedrichsComplementSqrt n hn=
      1-correspondenceOperatorComplexResolvent n hn :=
  CFC.sqrt_mul_sqrt_self _ (correspondenceFriedrichs_one_sub_resolvent_nonneg n hn)

theorem correspondenceFriedrichsComplementSqrt_selfAdjoint (n : ℕ) (hn : 0<n) :
    IsSelfAdjoint (correspondenceFriedrichsComplementSqrt n hn) := by
  unfold correspondenceFriedrichsComplementSqrt
  exact (CFC.sqrt_nonneg (1-correspondenceOperatorComplexResolvent n hn)).isSelfAdjoint

theorem correspondenceFriedrichsSquareRoots_commute (n : ℕ) (hn : 0<n) :
    Commute (correspondenceFriedrichsResolventSqrt n hn) (correspondenceFriedrichsComplementSqrt n hn) := by
  have h : Commute (correspondenceOperatorComplexResolvent n hn) (1-correspondenceOperatorComplexResolvent n hn) :=
    (Commute.one_right _).sub_right (Commute.refl _)
  have h1:=h.cfcₙ_nnreal NNReal.sqrt
  have h2:=h1.symm.cfcₙ_nnreal NNReal.sqrt
  exact h2.symm

theorem correspondenceFriedrichsSquareRoots_sum_squares (n : ℕ) (hn : 0<n)
    (x : GinibreFullComplexL2 n) :
    correspondenceFriedrichsResolventSqrt n hn (correspondenceFriedrichsResolventSqrt n hn x)+
      correspondenceFriedrichsComplementSqrt n hn (correspondenceFriedrichsComplementSqrt n hn x)=x := by
  rw [← mul_apply_eq_comp,← mul_apply_eq_comp,correspondenceFriedrichsResolventSqrt_square,
    correspondenceFriedrichsComplementSqrt_square]
  simp

#print axioms correspondenceFriedrichsSquareRoots_sum_squares
end
end GinibrePoincare
