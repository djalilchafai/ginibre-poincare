module

public import GinibrePoincare.Analysis.NonQuadraticDbarAdjoint
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

@[expose] public section

/-! # Weak solvability from adjoint coercivity
The duality construction does not assume an analytic solution or a closed
operator domain. It extends the bounded functional on the actual adjoint
range and applies the Hilbert space Riesz representation theorem. -/
namespace GinibrePoincare
noncomputable section
open scoped InnerProductSpace
set_option maxHeartbeats 600000

/-- Hahn–Banach/Riesz weak solvability from a coercive test operator.
`V` is the embedding of tests and `A` their adjoint image; no norm on the
algebraic test space is required. -/
theorem exists_weak_solution_of_adjoint_bound
    {D H : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A V : D →ₗ[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, ‖V φ‖ ≤ C * ‖A φ‖) (h : H) :
    ∃ u : H, ‖u‖ ≤ C * ‖h‖ ∧ ∀ φ, ⟪u, A φ⟫_ℝ = ⟪h, V φ⟫_ℝ := by
  let F : D →ₗ[ℝ] ℝ := (innerSL ℝ h).toLinearMap.comp V
  have hker : A.ker ≤ F.ker := by
    intro φ hφ
    have hzero : V φ = 0 := by
      have hh := hbound φ
      have hA : A φ = 0 := hφ
      rw [hA, norm_zero, mul_zero] at hh
      exact norm_eq_zero.mp (le_antisymm hh (norm_nonneg _))
    change ⟪h, V φ⟫_ℝ = 0
    rw [hzero, inner_zero_right]
  let L : A.range →ₗ[ℝ] ℝ :=
    (A.ker.liftQ F hker).comp A.quotKerEquivRange.symm.toLinearMap
  have hL (φ : D) : L ⟨A φ, ⟨φ, rfl⟩⟩ = ⟪h, V φ⟫_ℝ := by
    have he : A.quotKerEquivRange.symm ⟨A φ, ⟨φ, rfl⟩⟩ = Submodule.Quotient.mk φ := by
      apply A.quotKerEquivRange.injective
      rw [LinearEquiv.apply_symm_apply]
      apply Subtype.ext
      exact (LinearMap.quotKerEquivRange_apply_mk A φ).symm
    simp only [L, LinearMap.comp_apply, LinearEquiv.coe_coe, he, Submodule.liftQ_apply]
    rfl
  have hLb (x : A.range) : ‖L x‖ ≤ (‖h‖ * C) * ‖x‖ := by
    obtain ⟨φ, hφ⟩ := x.property
    have hx : x = ⟨A φ, ⟨φ, rfl⟩⟩ := Subtype.ext hφ.symm
    rw [hx, hL]
    calc
      ‖⟪h, V φ⟫_ℝ‖ ≤ ‖h‖ * ‖V φ‖ := norm_inner_le_norm _ _
      _ ≤ ‖h‖ * (C * ‖A φ‖) := mul_le_mul_of_nonneg_left (hbound φ) (norm_nonneg h)
      _ = (‖h‖ * C) * ‖(⟨A φ, ⟨φ, rfl⟩⟩ : A.range)‖ := by rw [mul_assoc]; rfl
  let T : A.range →L[ℝ] ℝ := L.mkContinuous (‖h‖ * C) hLb
  have hT : ‖T‖ ≤ ‖h‖ * C :=
    T.opNorm_le_bound (mul_nonneg (norm_nonneg h) hC) hLb
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq A.range T
  let u := (InnerProductSpace.toDual ℝ H).symm G
  refine ⟨u, ?_, ?_⟩
  · calc
      ‖u‖ = ‖G‖ := (InnerProductSpace.toDual ℝ H).symm.norm_map G
      _ = ‖T‖ := hnorm
      _ ≤ ‖h‖ * C := hT
      _ = C * ‖h‖ := mul_comm _ _
  · intro φ
    rw [show u = (InnerProductSpace.toDual ℝ H).symm G from rfl,
      InnerProductSpace.toDual_symm_apply]
    have hh := hG (⟨A φ, ⟨φ, rfl⟩⟩ : A.range)
    change G (A φ) = L ⟨A φ, ⟨φ, rfl⟩⟩ at hh
    rw [hh, hL]

/-- The same adjoint estimate gives the primal spectral gap on the closure
of the actual adjoint range, directly from the weak derivative pairing. -/
theorem norm_le_of_weak_pairing_and_range_closure
    {D H : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A V : D →ₗ[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, ‖V φ‖ ≤ C * ‖A φ‖) (f h : H)
    (hmem : f ∈ A.range.topologicalClosure)
    (hpair : ∀ φ, ⟪f, A φ⟫_ℝ = ⟪h, V φ⟫_ℝ) :
    ‖f‖ ≤ C * ‖h‖ := by
  let S := {x : H | ‖⟪f, x⟫_ℝ‖ ≤ (C * ‖h‖) * ‖x‖}
  have hclosed : IsClosed S :=
    isClosed_le ((innerSL ℝ f).continuous.norm) (continuous_const.mul continuous_norm)
  have hrange : (A.range : Set H) ⊆ S := by
    rintro x ⟨φ, rfl⟩
    change ‖⟪f, A φ⟫_ℝ‖ ≤ (C * ‖h‖) * ‖A φ‖
    rw [hpair]
    calc
      ‖⟪h, V φ⟫_ℝ‖ ≤ ‖h‖ * ‖V φ‖ := norm_inner_le_norm _ _
      _ ≤ ‖h‖ * (C * ‖A φ‖) := mul_le_mul_of_nonneg_left (hbound φ) (norm_nonneg h)
      _ = (C * ‖h‖) * ‖A φ‖ := by ring
  have hs : f ∈ S := closure_minimal hrange hclosed hmem
  change ‖⟪f, f⟫_ℝ‖ ≤ (C * ‖h‖) * ‖f‖ at hs
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] at hs
  by_cases hfzero : f = 0
  · subst f
    simpa using mul_nonneg hC (norm_nonneg h)
  · have hp : 0 < ‖f‖ := norm_pos_iff.mpr hfzero
    nlinarith

/-- Orthogonality to the weak kernel is exactly the condition needed for
the primal spectral gap; no smooth holomorphic identification is assumed. -/
theorem norm_le_of_weak_pairing_and_kernel_orthogonal
    {D H : Type*} [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (A V : D →ₗ[ℝ] H) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, ‖V φ‖ ≤ C * ‖A φ‖) (f h : H)
    (hmem : f ∈ A.rangeᗮᗮ)
    (hpair : ∀ φ, ⟪f, A φ⟫_ℝ = ⟪h, V φ⟫_ℝ) :
    ‖f‖ ≤ C * ‖h‖ := by
  rw [Submodule.orthogonal_orthogonal_eq_closure] at hmem
  exact norm_le_of_weak_pairing_and_range_closure A V C hC hbound f h hmem hpair

end
end GinibrePoincare
