module

public import GinibrePoincare.Concrete.Vandermonde
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.NNReal.Defs
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Gaussian and Ginibre weights

This file defines the Euclidean square norm, the Gaussian weight, the
Vandermonde square, and the unnormalised Ginibre density.  The zero set of the
latter is proved to be exactly the collision locus.
-/

open scoped BigOperators NNReal

namespace GinibrePoincare

noncomputable section

/-- Euclidean squared norm on `ℂ^n`. -/
def configurationNormSq {n : ℕ} (z : Configuration n) : ℝ :=
  ∑ i : Fin n, Complex.normSq (z i)

/-- The Gaussian factor `exp (-n |z|²)`. -/
def gaussianWeight (n : ℕ) (z : Configuration n) : ℝ :=
  Real.exp (-(n : ℝ) * configurationNormSq z)

/-- The nonnegative squared modulus of the Vandermonde determinant. -/
def vandermondeWeight {n : ℕ} (z : Configuration n) : ℝ :=
  Complex.normSq (vandermonde z)

/-- The unnormalised Ginibre density with respect to Lebesgue measure. -/
def ginibreWeight (n : ℕ) (z : Configuration n) : ℝ :=
  gaussianWeight n z * vandermondeWeight z

/-- The Euclidean squared norm is nonnegative. -/
theorem configurationNormSq_nonneg {n : ℕ} (z : Configuration n) :
    0 ≤ configurationNormSq z := by
  unfold configurationNormSq
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg (z i)

/-- The Gaussian factor is strictly positive. -/
theorem gaussianWeight_pos (n : ℕ) (z : Configuration n) :
    0 < gaussianWeight n z := by
  unfold gaussianWeight
  exact Real.exp_pos _

/-- The Gaussian factor is nonnegative. -/
theorem gaussianWeight_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ gaussianWeight n z :=
  le_of_lt (gaussianWeight_pos n z)

/-- The Vandermonde squared modulus is nonnegative. -/
theorem vandermondeWeight_nonneg {n : ℕ} (z : Configuration n) :
    0 ≤ vandermondeWeight z := by
  exact Complex.normSq_nonneg _

/-- The Ginibre density is nonnegative. -/
theorem ginibreWeight_nonneg (n : ℕ) (z : Configuration n) :
    0 ≤ ginibreWeight n z := by
  exact mul_nonneg (gaussianWeight_nonneg n z)
    (vandermondeWeight_nonneg z)

/-- The Gaussian weight as a nonnegative real number. -/
def gaussianWeightNN (n : ℕ) (z : Configuration n) : ℝ≥0 :=
  ⟨gaussianWeight n z, gaussianWeight_nonneg n z⟩

/-- The Vandermonde square as a nonnegative real number. -/
def vandermondeWeightNN {n : ℕ} (z : Configuration n) : ℝ≥0 :=
  ⟨vandermondeWeight z, vandermondeWeight_nonneg z⟩

/-- The Ginibre weight as a nonnegative real number. -/
def ginibreWeightNN (n : ℕ) (z : Configuration n) : ℝ≥0 :=
  ⟨ginibreWeight n z, ginibreWeight_nonneg n z⟩

@[simp]
theorem coe_gaussianWeightNN (n : ℕ) (z : Configuration n) :
    (gaussianWeightNN n z : ℝ) = gaussianWeight n z :=
  rfl

@[simp]
theorem coe_vandermondeWeightNN {n : ℕ} (z : Configuration n) :
    (vandermondeWeightNN z : ℝ) = vandermondeWeight z :=
  rfl

@[simp]
theorem coe_ginibreWeightNN (n : ℕ) (z : Configuration n) :
    (ginibreWeightNN n z : ℝ) = ginibreWeight n z :=
  rfl

/-- The Vandermonde square vanishes precisely at collisions. -/
theorem vandermondeWeight_eq_zero_iff {n : ℕ} (z : Configuration n) :
    vandermondeWeight z = 0 ↔ z ∈ collisionSet n := by
  rw [vandermondeWeight, Complex.normSq_eq_zero]
  exact vandermonde_eq_zero_iff z

/-- The Ginibre density vanishes precisely at collisions. -/
theorem ginibreWeight_eq_zero_iff (n : ℕ) (z : Configuration n) :
    ginibreWeight n z = 0 ↔ z ∈ collisionSet n := by
  unfold ginibreWeight
  rw [mul_eq_zero]
  constructor
  · intro h
    rcases h with hgauss | hvdm
    · exact False.elim ((ne_of_gt (gaussianWeight_pos n z)) hgauss)
    · exact (vandermondeWeight_eq_zero_iff z).mp hvdm
  · intro h
    exact Or.inr ((vandermondeWeight_eq_zero_iff z).mpr h)

/-- The Euclidean square norm is invariant under particle relabelling. -/
theorem configurationNormSq_permute {n : ℕ}
    (σ : ParticlePermutation n) (z : Configuration n) :
    configurationNormSq (permute σ z) = configurationNormSq z := by
  unfold configurationNormSq
  simpa [permute] using (Equiv.sum_comp σ (fun i => Complex.normSq (z i)))

/-- The Gaussian factor is invariant under particle relabelling. -/
theorem gaussianWeight_permute {n : ℕ}
    (σ : ParticlePermutation n) (z : Configuration n) :
    gaussianWeight n (permute σ z) = gaussianWeight n z := by
  simp [gaussianWeight, configurationNormSq_permute]

end

end GinibrePoincare
