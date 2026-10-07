module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import GinibrePoincare.Concrete.CenterOfMass
public import GinibrePoincare.Concrete.MeasureModel
public import GinibrePoincare.Concrete.Wirtinger
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Topology.Algebra.Support

@[expose] public section

/-!
# Exact smooth-core statement

This file gives the literal variance and gradient energy of the Ginibre
measure, together with the exact smooth-core Poincaré and sharpness
propositions.  These are definitions of the mathematical targets, not
asserted theorems.
-/

open MeasureTheory
open scoped ContDiff

namespace GinibrePoincare

noncomputable section

/-- Mean of a real observable under `μ_n`. -/
def smoothGinibreMean (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  ∫ z, f z ∂ginibreMeasure n

/-- Variance of a real observable under `μ_n`. -/
def smoothGinibreVariance (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  ∫ z, (f z - smoothGinibreMean n f) ^ 2 ∂ginibreMeasure n

/-- Euclidean pointwise squared norm of the real Fréchet derivative, expanded
in the real and imaginary coordinate directions.  This explicit formula is
necessary because the function-space norm on `Fin n → ℂ` is the sup norm,
whereas the Ginibre Dirichlet form uses the Euclidean product metric. -/
def realGradientNormSq {n : ℕ} (f : Configuration n → ℝ)
    (z : Configuration n) : ℝ :=
  ∑ k : Fin n, (
    (fderiv ℝ f z (realCoordinateDirection k)) ^ 2 +
      (fderiv ℝ f z (imaginaryCoordinateDirection k)) ^ 2)

/-- Dirichlet energy in the normalization of the paper. -/
def smoothGinibreEnergy (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  (1 / (n : ℝ)) *
    ∫ z, realGradientNormSq f z ∂ginibreMeasure n

/-- Smooth, compactly supported, coordinate-symmetric real observables. -/
def IsSmoothCompactSymmetric {n : ℕ}
    (f : Configuration n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ IsSymmetric f

/-- The optimal smooth-core Poincaré theorem, written as one exact proposition. -/
def SmoothGinibrePoincareStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      smoothGinibreVariance n f ≤ smoothGinibreEnergy n f / 2

/-- Equality statement for the real center-of-mass direction. -/
def RealCenterSharpnessStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    IsProbabilityMeasure (ginibreMeasure n) →
    smoothGinibreVariance n
        (fun z : Configuration n => centerOfMassReal z) =
      smoothGinibreEnergy n
        (fun z : Configuration n => centerOfMassReal z) / 2

/-- Equality statement for the imaginary center-of-mass direction. -/
def ImagCenterSharpnessStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    IsProbabilityMeasure (ginibreMeasure n) →
    smoothGinibreVariance n
        (fun z : Configuration n => centerOfMassImag z) =
      smoothGinibreEnergy n
        (fun z : Configuration n => centerOfMassImag z) / 2

end

end GinibrePoincare
