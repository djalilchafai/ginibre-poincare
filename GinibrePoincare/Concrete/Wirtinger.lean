module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import GinibrePoincare.Concrete.MeasureModel
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

@[expose] public section

/-!
# Concrete Wirtinger derivatives and Gaussian holomorphic distance

The coordinate operators
`∂̄_k = (∂_{x_k} + i ∂_{y_k}) / 2` are defined directly from the real
Fréchet derivative on `Configuration n`.
-/

open MeasureTheory
open scoped BigOperators ContDiff

namespace GinibrePoincare

noncomputable section

/-- A vector supported in one complex coordinate. -/
def coordinateDirection {n : ℕ} (k : Fin n) (w : ℂ) :
    Configuration n :=
  fun j => if j = k then w else 0

/-- Unit direction in the real part of coordinate `k`. -/
def realCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k 1

/-- Unit direction in the imaginary part of coordinate `k`. -/
def imaginaryCoordinateDirection {n : ℕ} (k : Fin n) :
    Configuration n :=
  coordinateDirection k Complex.I

/-- Coordinate `∂̄` derivative defined from the real Fréchet derivative. -/
def dbarComponent {n : ℕ} (g : Configuration n → ℂ)
    (k : Fin n) (z : Configuration n) : ℂ :=
  (1 / 2 : ℂ) *
    (fderiv ℝ g z (realCoordinateDirection k) +
      Complex.I * fderiv ℝ g z (imaginaryCoordinateDirection k))

/-- Sum of the squared coordinate `∂̄` derivatives at a point. -/
def dbarNormSq {n : ℕ} (g : Configuration n → ℂ)
    (z : Configuration n) : ℝ :=
  ∑ k : Fin n, Complex.normSq (dbarComponent g k z)

/-- Normalized Gaussian `∂̄` energy. -/
def gaussianDbarEnergy (n : ℕ) (g : Configuration n → ℂ) : ℝ :=
  (1 / (n : ℝ)) *
    ∫ z, dbarNormSq g z ∂complexGaussianMeasure n

/-- Entire functions on the finite-dimensional complex configuration space. -/
def IsEntire {n : ℕ} (h : Configuration n → ℂ) : Prop :=
  Differentiable ℂ h

/-- Square-integrability of a complex function for the Gaussian measure. -/
def IsGaussianL2 (n : ℕ) (g : Configuration n → ℂ) : Prop :=
  Integrable (fun z => Complex.normSq (g z))
    (complexGaussianMeasure n)

/-- Form-domain conditions used by the representative-level `∂̄` estimate. -/
def IsGaussianDbarAdmissible (n : ℕ)
    (g : Configuration n → ℂ) : Prop :=
  ContDiff ℝ ∞ g ∧ IsGaussianL2 n g ∧
    ∀ k : Fin n,
      Integrable (fun z => Complex.normSq (dbarComponent g k z))
        (complexGaussianMeasure n)

/-- Squared Gaussian `L²` error between two complex functions. -/
def gaussianComplexError (n : ℕ) (g h : Configuration n → ℂ) : ℝ :=
  ∫ z, Complex.normSq (g z - h z) ∂complexGaussianMeasure n

/-- Set of errors of entire square-integrable Gaussian approximants. -/
def gaussianHolomorphicErrors (n : ℕ)
    (g : Configuration n → ℂ) : Set ℝ :=
  {r | ∃ h : Configuration n → ℂ,
    IsEntire h ∧ IsGaussianL2 n h ∧
      r = gaussianComplexError n g h}

/-- Squared distance to the Gaussian holomorphic subspace, on representatives. -/
def gaussianHolomorphicDistanceSq (n : ℕ)
    (g : Configuration n → ℂ) : ℝ :=
  sInf (gaussianHolomorphicErrors n g)

/-- Exact target for the Gaussian `∂̄` estimate. -/
def GaussianDbarEstimateStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    ∀ g : Configuration n → ℂ,
      IsGaussianDbarAdmissible n g →
      gaussianHolomorphicDistanceSq n g ≤ gaussianDbarEnergy n g

end

end GinibrePoincare
