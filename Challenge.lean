module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Topology.Algebra.Support
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

/-!
# Independent Ginibre statement surface

Source: https://arxiv.org/abs/2608.19358v2, Theorem 1.1.
This Comparator surface records the full symmetric weak-H¹ Poincaré inequality
with the paper's constant `1 / (2n)` and its exhaustive affine equality case. The substantive
repository also proves deficit, dynamical and matrix results;
those additional statements are not advertised by this particular comparison.

Each real Gaussian coordinate below has variance `1 / (2n)`. Its complex
product density is `(n/π)^n exp(-n ∑ |zᵢ|²)`. Weighting by the squared
Vandermonde determinant and dividing by its actual total mass gives the
concrete normalized Ginibre law, without any assumed normalization fact.
The energy uses the Euclidean coordinate gradient, rather than the sup norm
on Lean's function space `Fin n → ℂ`.

Only pinned Mathlib modules are imported. These definitions are independently
spelled out and compared with their implementations in the Solution closure.
-/

open MeasureTheory
open scoped BigOperators ContDiff ENNReal Topology

namespace GinibrePoincare
noncomputable section

/-- Configurations of `n` complex particles. -/
abbrev Configuration (n : ℕ) := Fin n → ℂ
/-- Permutations of particle labels. -/
abbrev ParticlePermutation (n : ℕ) := Equiv.Perm (Fin n)
/-- Relabel a configuration by a permutation. -/
def permute {n : ℕ} (σ : ParticlePermutation n) (z : Configuration n) : Configuration n :=
  fun i => z (σ i)
/-- Invariance under every relabeling. -/
def IsSymmetric {n : ℕ} {α : Type*} (f : Configuration n → α) : Prop :=
  ∀ (σ : ParticlePermutation n) (z : Configuration n), f (permute σ z) = f z
/-- The Vandermonde determinant `∏ᵢ ∏ⱼ>ᵢ (zⱼ-zᵢ)`. -/
def vandermonde {n : ℕ} (z : Configuration n) : ℂ := (Matrix.vandermonde z).det
/-- Squared modulus of the Vandermonde determinant. -/
def vandermondeWeight {n : ℕ} (z : Configuration n) : ℝ :=
  Complex.normSq (vandermonde z)
/-- Variance of each real Gaussian coordinate. -/
def realCoordinateVariance (n : ℕ) : NNReal := ((2 : NNReal) * (n : NNReal))⁻¹
/-- Centered real Gaussian probability distribution. -/
def realCoordinateGaussianProbability (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨ProbabilityTheory.gaussianReal 0 (realCoordinateVariance n), by infer_instance⟩
/-- One complex coordinate made from two independent real Gaussians. -/
def complexCoordinateGaussianProbability (n : ℕ) : ProbabilityMeasure ℂ :=
  (ProbabilityMeasure.pi (fun _ : Fin 2 => realCoordinateGaussianProbability n)).map
    Complex.measurableEquivPi.symm
/-- Independent complex Gaussian coordinates. -/
def complexGaussianProbability (n : ℕ) : ProbabilityMeasure (Configuration n) :=
  ProbabilityMeasure.pi (fun _ : Fin n => complexCoordinateGaussianProbability n)
/-- Gaussian product law as an ordinary measure. -/
def complexGaussianMeasure (n : ℕ) : Measure (Configuration n) :=
  (complexGaussianProbability n : Measure (Configuration n))
/-- Nonnegative Vandermonde density. -/
def vandermondeDensity {n : ℕ} (z : Configuration n) : ℝ≥0∞ :=
  ENNReal.ofReal (vandermondeWeight z)
/-- Unnormalized Ginibre law. -/
def rawGinibreMeasure (n : ℕ) : Measure (Configuration n) :=
  (complexGaussianMeasure n).withDensity vandermondeDensity
/-- Actual mass of the unnormalized law. -/
def ginibreNormalizingMass (n : ℕ) : ℝ≥0∞ := rawGinibreMeasure n Set.univ
/-- Normalized Ginibre probability law. -/
def ginibreMeasure (n : ℕ) : Measure (Configuration n) :=
  (ginibreNormalizingMass n)⁻¹ • rawGinibreMeasure n
/-- Vector supported in coordinate `k` with value `w`. -/
def coordinateDirection {n : ℕ} (k : Fin n) (w : ℂ) : Configuration n :=
  fun j => if j = k then w else 0
/-- Unit real coordinate direction. -/
def realCoordinateDirection {n : ℕ} (k : Fin n) : Configuration n := coordinateDirection k 1
/-- Unit imaginary coordinate direction. -/
def imaginaryCoordinateDirection {n : ℕ} (k : Fin n) : Configuration n :=
  coordinateDirection k Complex.I
/-- Mean of a real observable under the Ginibre law. -/
def smoothGinibreMean (n : ℕ) (f : Configuration n → ℝ) : ℝ := ∫ z, f z ∂ginibreMeasure n
/-- Variance of a real observable under the Ginibre law. -/
def smoothGinibreVariance (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  ∫ z, (f z - smoothGinibreMean n f) ^ 2 ∂ginibreMeasure n
/-- Squared Euclidean gradient norm, in real and imaginary directions. -/
def realGradientNormSq {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  ∑ k : Fin n, ((fderiv ℝ f z (realCoordinateDirection k)) ^ 2 +
    (fderiv ℝ f z (imaginaryCoordinateDirection k)) ^ 2)
/-- Paper-normalized Dirichlet energy. -/
def smoothGinibreEnergy (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  (1 / (n : ℝ)) * ∫ z, realGradientNormSq f z ∂ginibreMeasure n
/-- Smooth compactly supported permutation-invariant real observables. -/
def IsSmoothCompactSymmetric {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ IsSymmetric f

/-- Collision-free configurations: all particles have distinct coordinates. -/
def CollisionFree {n : ℕ} (z : Configuration n) : Prop := Function.Injective z
/-- Real or imaginary coordinate direction, indexed by `Fin n × Fin 2`. -/
def ginibreCoordinateDirection {n : ℕ} (k : Fin n × Fin 2) : Configuration n :=
  if k.2 = 0 then realCoordinateDirection k.1 else imaginaryCoordinateDirection k.1
/-- Ordinary distributional gradient on the collision-free open set.
The integrals in this definition are with respect to ordinary Lebesgue volume;
values and gradients themselves belong to the concrete weighted Ginibre L² spaces.
Local Lebesgue integrability and testing against every smooth interior compact
test are explicit, so this is the actual weak derivative, not a certificate. -/
def IsGinibreDistributionalGradient (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : Prop :=
  LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume ∧
    (∀ k : Fin n × Fin 2,
      LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume) ∧
    ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
      ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))
/-- Weak Dirichlet energy in the paper's normalization. -/
def ginibreWeakEnergy (n : ℕ)
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) : ℝ :=
  (1 / (n : ℝ)) * ‖g‖ ^ 2
/-- Sum of complex particle coordinates. -/
def coordinateSum {n : ℕ} (z : Configuration n) : ℂ := ∑ j : Fin n, z j

end
end GinibrePoincare

namespace PalomarGinibre
open GinibrePoincare
/-- Full weak-H¹ symmetric Poincaré assertion and exact affine equality case.
Symmetry is imposed only on the observable; its weak gradient's corresponding
symmetry follows from uniqueness, rather than being an additional assumption. -/
def theoremOneOneStatement : Prop :=
  ∀ n : ℕ, 0 < n → ∀ u : Lp ℝ 2 (ginibreMeasure n),
    ∀ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      IsGinibreDistributionalGradient n u g →
      (∀ σ : ParticlePermutation n,
        (fun z => u (permute σ z)) =ᵐ[ginibreMeasure n] (u : Configuration n → ℝ)) →
      smoothGinibreVariance n u ≤ ginibreWeakEnergy n g / 2 ∧
        (smoothGinibreVariance n u = ginibreWeakEnergy n g / 2 ↔
          ∃ (a : ℝ) (c : ℂ), (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
            fun z => a + 2 * (c * coordinateSum z).re)

/-- Independent statement-only target; the proved version is in Solution. -/
theorem theoremOneOne :
  ∀ n : ℕ, 0 < n → ∀ u : Lp ℝ 2 (ginibreMeasure n),
    ∀ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume ∧
        (∀ k : Fin n × Fin 2,
          LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume) ∧
        ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
          ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
            (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))) →
      (∀ σ : ParticlePermutation n,
        (fun z => u (permute σ z)) =ᵐ[ginibreMeasure n] (u : Configuration n → ℝ)) →
      smoothGinibreVariance n u ≤ ((1 / (n : ℝ)) * ‖g‖ ^ 2) / 2 ∧
        (smoothGinibreVariance n u = ((1 / (n : ℝ)) * ‖g‖ ^ 2) / 2 ↔
          ∃ (a : ℝ) (c : ℂ), (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
            fun z => a + 2 * (c * coordinateSum z).re) := by
  sorry

end PalomarGinibre
