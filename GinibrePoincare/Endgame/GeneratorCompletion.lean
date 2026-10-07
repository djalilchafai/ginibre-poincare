module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Universal Hilbert-space square completion

Equation (6.6) of the paper is independent of the Ginibre realization.  This
file proves it directly for a real-linear operator on a real inner-product
space.  There is no certificate, no measure-theoretic hypothesis, and no
Ginibre-specific theorem hidden in the declarations.
-/

namespace GinibrePoincare

noncomputable section

namespace OperatorSquareCompletion

variable {E : Type*}
variable [SeminormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- Squared norm, written as a real inner product. -/
def normSq (f : E) : ℝ :=
  inner ℝ f f

/-- Variance of a centered vector in the abstract Hilbert calculation. -/
def variance (f : E) : ℝ :=
  normSq f

/-- Dirichlet energy associated with a real-linear generator. -/
def energy (A : E →ₗ[ℝ] E) (f : E) : ℝ :=
  -inner ℝ (A f) f

/-- Squared norm of the generator image. -/
def generatorSq (A : E →ₗ[ℝ] E) (f : E) : ℝ :=
  normSq (A f)

/-- Squared norm of `(A + 2 I)f`. -/
def shiftedGeneratorSq (A : E →ₗ[ℝ] E) (f : E) : ℝ :=
  normSq (A f + (2 : ℝ) • f)

/-- A squared norm is nonnegative. -/
theorem normSq_nonneg (f : E) :
    0 ≤ normSq f := by
  exact real_inner_self_nonneg

/-- The shifted-generator square is nonnegative. -/
theorem shiftedGeneratorSq_nonneg (A : E →ₗ[ℝ] E) (f : E) :
    0 ≤ shiftedGeneratorSq A f := by
  exact normSq_nonneg (A f + (2 : ℝ) • f)

/-- Direct expansion of the shifted square. -/
theorem shiftedGeneratorSq_expand (A : E →ₗ[ℝ] E) (f : E) :
    shiftedGeneratorSq A f =
      generatorSq A f - 4 * energy A f + 4 * variance f := by
  unfold shiftedGeneratorSq generatorSq energy variance normSq
  have hcomm : inner ℝ f (A f) = inner ℝ (A f) f :=
    real_inner_comm (A f) f
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, hcomm]
  ring

/-- Equation (6.6), proved by expanding the square. -/
theorem completionSquare (A : E →ₗ[ℝ] E) (f : E) :
    generatorSq A f - 2 * energy A f =
      shiftedGeneratorSq A f +
        2 * (energy A f - 2 * variance f) := by
  rw [shiftedGeneratorSq_expand]
  ring

/-- Poincaré implies the integrated `Gamma_2` inequality by square completion. -/
theorem integratedGammaTwo_of_poincare
    (A : E →ₗ[ℝ] E)
    (f : E)
    (hPoincare : 2 * variance f ≤ energy A f) :
    2 * energy A f ≤ generatorSq A f := by
  have hSquare := completionSquare A f
  have hShifted := shiftedGeneratorSq_nonneg A f
  linarith

end OperatorSquareCompletion

end

end GinibrePoincare
