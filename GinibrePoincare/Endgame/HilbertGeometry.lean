module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap

@[expose] public section

/-!
# Hilbert-space geometry used by the Ginibre deficit proof

This file isolates the Pythagorean part of the proof.  It proves the norm
identity obtained from three pairwise orthogonal vectors, and the particular
zero-mode geometry

`‖f‖² = 2 ‖h‖² + ‖r‖²`

when `f = h + hbar + r`, the three summands are pairwise orthogonal, and
`‖hbar‖ = ‖h‖`.
-/

namespace GinibrePoincare

noncomputable section

/-- The square of the norm, written without using a power. -/
def normSq {E : Type*} [Norm E] (x : E) : ℝ :=
  ‖x‖ * ‖x‖

@[simp]
theorem normSq_zero {E : Type*} [SeminormedAddCommGroup E] :
    normSq (0 : E) = 0 := by
  simp [normSq]

/-- A squared norm is nonnegative. -/
theorem normSq_nonneg {E : Type*} [SeminormedAddCommGroup E] (x : E) :
    0 ≤ normSq x := by
  exact mul_self_nonneg ‖x‖

/-- Pythagoras in the notation `normSq`. -/
theorem normSq_add_of_inner_eq_zero
    {𝕜 E : Type*}
    [RCLike 𝕜]
    [SeminormedAddCommGroup E]
    [InnerProductSpace 𝕜 E]
    (x y : E)
    (hxy : inner 𝕜 x y = 0) :
    normSq (x + y) = normSq x + normSq y := by
  simpa only [normSq] using
    norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero x y hxy

/-- Pythagoras for three pairwise orthogonal vectors in a real inner-product space. -/
theorem normSq_three_of_pairwise_orthogonal
    {E : Type*}
    [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (x y z : E)
    (hxy : inner ℝ x y = 0)
    (hxz : inner ℝ x z = 0)
    (hyz : inner ℝ y z = 0) :
    normSq (x + y + z) = normSq x + normSq y + normSq z := by
  have hsumz : inner ℝ (x + y) z = 0 := by
    simp only [inner_add_left, hxz, hyz, add_zero]
  calc
    normSq (x + y + z) = normSq (x + y) + normSq z :=
      normSq_add_of_inner_eq_zero (x + y) z hsumz
    _ = normSq x + normSq y + normSq z := by
      rw [normSq_add_of_inner_eq_zero x y hxy]

/--
The abstract Hilbert-space form of the holomorphic--antiholomorphic
projection geometry used in the paper.
-/
theorem zero_mode_projection_geometry
    {E : Type*}
    [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    (f h hbar r : E)
    (hf : f = h + hbar + r)
    (hh_hbar : inner ℝ h hbar = 0)
    (hh_r : inner ℝ h r = 0)
    (hhbar_r : inner ℝ hbar r = 0)
    (hNorm : ‖hbar‖ = ‖h‖) :
    normSq f = 2 * normSq h + normSq r := by
  rw [hf, normSq_three_of_pairwise_orthogonal h hbar r hh_hbar hh_r hhbar_r]
  unfold normSq
  rw [hNorm]
  ring

/-- A linear isometric equivalence preserves squared norms. -/
@[simp]
theorem normSq_map_linearIsometryEquiv
    {𝕜 E F : Type*}
    [RCLike 𝕜]
    [SeminormedAddCommGroup E]
    [SeminormedAddCommGroup F]
    [NormedSpace 𝕜 E]
    [NormedSpace 𝕜 F]
    (U : E ≃ₗᵢ[𝕜] F)
    (x : E) :
    normSq (U x) = normSq x := by
  simp [normSq]

end

end GinibrePoincare
