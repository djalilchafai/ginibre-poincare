module
public import GinibrePoincare.Analysis.CorrespondenceOperatorComplex
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
public import Mathlib.Analysis.Normed.Operator.Extend
@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

/-- The range theorem needed for the closed-form square-root representation.
It follows from extending the literal norm-preserving map on a dense range. -/
theorem correspondenceSquareRoot_adjoint_range
    {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    (A : H→L[ℝ]K) (B : H→L[ℝ]H) (hB : B.adjoint=B)
    (hd : DenseRange B) (hn : ∀x,‖A x‖=‖B x‖) :
    range A.adjoint=range B := by
  let U := A.toLinearMap.extendOfIsometry (e:=B.toLinearMap) hd hn
  have he : A=U.toContinuousLinearMap.comp B := by
    ext x
    exact (LinearMap.extendOfIsometry_eq A.toLinearMap hd hn x).symm
  have hadj : A.adjoint=B.comp U.toContinuousLinearMap.adjoint := by
    rw [he,ContinuousLinearMap.adjoint_comp,hB]
  rw [hadj]
  apply Subset.antisymm
  · rintro y ⟨x,rfl⟩
    exact ⟨U.toContinuousLinearMap.adjoint x,rfl⟩
  · rintro y ⟨x,rfl⟩
    refine ⟨U x,?_⟩
    have h:=congrArg (fun L : H→L[ℝ]H=>L x) U.adjoint_comp_self
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply,one_apply_eq_self,LinearIsometry.coe_toContinuousLinearMap] using congrArg B h

/-- The bounded functional-calculus square root of the actual resolvent. -/
def correspondenceFriedrichsResolventSqrt (n : ℕ) (hn : 0<n) :
    GinibreFullComplexL2 n→L[ℂ]GinibreFullComplexL2 n :=
  CFC.sqrt (correspondenceOperatorComplexResolvent n hn)

theorem correspondenceFriedrichsResolventSqrt_square (n : ℕ) (hn : 0<n) :
    correspondenceFriedrichsResolventSqrt n hn*correspondenceFriedrichsResolventSqrt n hn=
      correspondenceOperatorComplexResolvent n hn := by
  exact CFC.sqrt_mul_sqrt_self _ (ContinuousLinearMap.nonneg_iff_isPositive.mpr (correspondenceOperatorComplexResolvent_isPositive n hn))

theorem correspondenceFriedrichsResolventSqrt_selfAdjoint (n : ℕ) (hn : 0<n) :
    IsSelfAdjoint (correspondenceFriedrichsResolventSqrt n hn) :=
  by
    unfold correspondenceFriedrichsResolventSqrt
    exact (CFC.sqrt_nonneg (correspondenceOperatorComplexResolvent n hn)).isSelfAdjoint

theorem correspondenceFriedrichsResolventSqrt_injective (n : ℕ) (hn : 0<n) :
    Function.Injective (correspondenceFriedrichsResolventSqrt n hn) := by
  intro x y h
  apply correspondenceOperatorComplexResolvent_injective n hn
  have he:=congrArg (correspondenceFriedrichsResolventSqrt n hn) h
  simpa only [← ContinuousLinearMap.mul_apply,correspondenceFriedrichsResolventSqrt_square] using he

theorem correspondenceFriedrichsResolventSqrt_denseRange (n : ℕ) (hn : 0<n) :
    DenseRange (correspondenceFriedrichsResolventSqrt n hn) := by
  apply (correspondenceOperatorComplexResolvent_denseRange n hn).mono
  rintro y ⟨x,rfl⟩
  refine ⟨correspondenceFriedrichsResolventSqrt n hn x,?_⟩
  exact congrArg (fun L : GinibreFullComplexL2 n→L[ℂ]GinibreFullComplexL2 n=>L x)
    (correspondenceFriedrichsResolventSqrt_square n hn)

#print axioms correspondenceFriedrichsResolventSqrt_square
end
end GinibrePoincare
