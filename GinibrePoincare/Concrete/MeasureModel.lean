module

public import GinibrePoincare.Concrete.Weights
public import GinibrePoincare.Concrete.GaussianProbability
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Data.ENNReal.Real

@[expose] public section

/-!
# Concrete Gaussian density and Ginibre measure

The Gaussian reference measure `complexGaussianMeasure n` is constructed in
`GaussianProbability.lean` as a genuine finite product probability measure.
This file also defines the explicit density measure

`(n / π)^n exp (-n |z|²) dz`.

Equality of these two descriptions is stated explicitly as
`ComplexGaussianDensityIdentificationStatement`; it is not hidden in a
definition.  The unnormalised Ginibre measure is then `|V_n|² γ_n`, and its
actual total mass is used for normalization.
-/

open MeasureTheory
open scoped ENNReal

namespace GinibrePoincare

noncomputable section

/-- Canonical Lebesgue/Haar volume on the finite-dimensional real space `ℂⁿ`. -/
def configurationVolume (n : ℕ) : Measure (Configuration n) :=
  volume

/-- Explicit density of the normalized complex Gaussian reference measure. -/
def complexGaussianDensity (n : ℕ) (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((((n : ℝ) / Real.pi) ^ n) * gaussianWeight n z)

/-- Measure defined directly by the explicit Gaussian density. -/
def complexGaussianDensityMeasure (n : ℕ) : Measure (Configuration n) :=
  (configurationVolume n).withDensity (complexGaussianDensity n)

/-- Identification of the product Gaussian law with its explicit Lebesgue
 density.  This is the remaining Gaussian density theorem. -/
def ComplexGaussianDensityIdentificationStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    complexGaussianMeasure n = complexGaussianDensityMeasure n

/-- Once the density identification is available, normalization of the
explicit density follows from the already proved probability normalization. -/
theorem complexGaussianDensityMeasure_univ_of_identification
    (h : ComplexGaussianDensityIdentificationStatement)
    (n : ℕ) (hn : 0 < n) :
    complexGaussianDensityMeasure n Set.univ = 1 := by
  rw [← h n hn]
  exact complexGaussianMeasure_univ n

/-- Vandermonde density as an extended nonnegative real. -/
def vandermondeDensity {n : ℕ} (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z)

/-- The unnormalised measure `|V_n|² γ_n`. -/
def rawGinibreMeasure (n : ℕ) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity vandermondeDensity

/-- Actual total mass of the unnormalised Ginibre measure. -/
def ginibreNormalizingMass (n : ℕ) : ℝ≥0∞ :=
  rawGinibreMeasure n Set.univ

/-- The normalized Ginibre measure `μ_n`. -/
def ginibreMeasure (n : ℕ) : Measure (Configuration n) :=
  (ginibreNormalizingMass n)⁻¹ • rawGinibreMeasure n

/-- Positivity and finiteness of the actual normalizing mass. -/
def GinibreMassIsValid (n : ℕ) : Prop :=
  0 < ginibreNormalizingMass n ∧ ginibreNormalizingMass n < ⊤

/-- Exact Selberg/Gram determinant normalization statement for the Ginibre gas. -/
def GinibreMassEvaluationStatement : Prop :=
  ∀ n : ℕ, 0 < n → GinibreMassIsValid n

/-- Exact probability-measure statement for the normalized Ginibre law. -/
def GinibreMeasureIsProbabilityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    ginibreMeasure n Set.univ = 1

/-- Normalizing by a positive finite raw mass produces total mass one. -/
theorem ginibreMeasure_univ_of_mass_valid (n : ℕ)
    (h : GinibreMassIsValid n) :
    ginibreMeasure n Set.univ = 1 := by
  rcases h with ⟨hpos, htop⟩
  simp only [ginibreMeasure, Measure.smul_apply, ginibreNormalizingMass]
  exact ENNReal.inv_mul_cancel hpos.ne' htop.ne

/-- A positive finite raw mass equips the normalized Ginibre measure with the
usual probability-measure typeclass. -/
theorem ginibreMeasure_isProbabilityMeasure_of_mass_valid (n : ℕ)
    (h : GinibreMassIsValid n) :
    IsProbabilityMeasure (ginibreMeasure n) :=
  ⟨ginibreMeasure_univ_of_mass_valid n h⟩

/-- The mass-validity theorem implies the probability-measure theorem. -/
theorem ginibreMeasureIsProbability_of_mass_evaluation
    (h : GinibreMassEvaluationStatement) :
    GinibreMeasureIsProbabilityStatement := by
  intro n hn
  exact ginibreMeasure_univ_of_mass_valid n (h n hn)

/-- Mass evaluation supplies the probability typeclass at every positive
particle number. -/
theorem ginibreMeasure_isProbabilityMeasure_of_mass_evaluation
    (h : GinibreMassEvaluationStatement) (n : ℕ) (hn : 0 < n) :
    IsProbabilityMeasure (ginibreMeasure n) :=
  ginibreMeasure_isProbabilityMeasure_of_mass_valid n (h n hn)

end

end GinibrePoincare
