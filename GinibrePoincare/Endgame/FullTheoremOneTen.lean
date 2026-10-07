module

public import GinibrePoincare.Analysis.GaussianDbarSmoothTests
public import GinibrePoincare.Endgame.FullTheoremOneNine
public import GinibrePoincare.Analysis.HermiteSecondDbarWeakClosure
public import GinibrePoincare.Analysis.HermiteSecondDbarInfiniteEnergy

@[expose] public section

/-! # Differential deficit vector and its genuine weak derivatives

The vector is the inverse square root of the antiholomorphic number operator
applied to the positive-mode projection of the actual centered Vandermonde
transform. Its weak derivatives follow from the concrete Ginibre weak gradient.
-/
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

def ginibreDifferentialDeficitVector (n : ℕ) (hn : 0 < n) (u : GinibreFullValueL2 n) :
    Lp ℂ 2 (complexGaussianMeasure n) :=
  gaussianHermiteInverseSquareRoot hn
    (ginibreFullCenteredTransform n hn u -
      gaussianHermiteMode hn 0 (ginibreFullCenteredTransform n hn u))

def ginibreDifferentialFirstDerivative (n : ℕ) (hn : 0 < n)
    (g : GinibreFullGradientL2 n) (j : Fin n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  gaussianInverseSquareRootFirstSynthesis hn (ginibreFullTransformedDbar n hn j g) j

def ginibreDifferentialSecondDerivative (n : ℕ) (hn : 0 < n)
    (g : GinibreFullGradientL2 n) (j k : Fin n) : Lp ℂ 2 (complexGaussianMeasure n) :=
  gaussianInverseSquareRootSecondSynthesis hn (ginibreFullTransformedDbar n hn j g) j k

/-- Actual weak first and second Wirtinger derivatives for every symmetric
ordinary Ginibre weak pair, without a spectral-domain assumption. -/
theorem ginibreDifferentialDeficit_weak_derivatives {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    (∀ j, IsGaussianWeakDbar n (ginibreDifferentialDeficitVector n hn u)
      (ginibreDifferentialFirstDerivative n hn g j) j) ∧
    (∀ j k, IsGaussianWeakDbar n (ginibreDifferentialFirstDerivative n hn g j)
      (ginibreDifferentialSecondDerivative n hn g j k) k) := by
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  have hcoeff := ginibreFullTransformedDbar_weak_coefficient hn
    (ginibreFullCenter n hn u) g huc hsc
  have hweak := gaussianInverseSquareRoot_weak_derivatives hn
    (ginibreFullCenteredTransform n hn u) (ginibreFullTransformedDbar n hn · g) hcoeff
  simpa only [ginibreDifferentialDeficitVector,
    gaussianHermiteInverseSquareRoot_positiveProjection,
    ginibreDifferentialFirstDerivative, ginibreDifferentialSecondDerivative] using hweak

def ginibreDifferentialSecondEnergy (n : ℕ) (hn : 0 < n)
    (g : GinibreFullGradientL2 n) : ℝ :=
  ∑ j : Fin n, ∑ k : Fin n, ‖ginibreDifferentialSecondDerivative n hn g j k‖ ^ 2

theorem gaussianL2_norm_sq_eq_integral_normSq {n : ℕ}
    (q : Lp ℂ 2 (complexGaussianMeasure n)) :
    ‖q‖ ^ 2 = ∫ z, Complex.normSq (q z) ∂complexGaussianMeasure n := by
  have hinner : inner ℂ q q =
      ∫ z, inner ℂ (q z) (q z) ∂complexGaussianMeasure n :=
    MeasureTheory.L2.inner_def q q
  rw [inner_self_eq_norm_sq_to_K] at hinner
  have hi : (fun z => inner ℂ (q z) (q z)) =
      fun z => (Complex.normSq (q z) : ℂ) := by
    funext z
    rw [inner_self_eq_norm_sq_to_K]
    calc
      (‖q z‖ : ℂ) ^ 2 = ((‖q z‖ ^ 2 : ℝ) : ℂ) := by norm_cast
      _ = _ := congrArg Complex.ofReal (Complex.sq_norm (q z))
  rw [hi, integral_complex_ofReal] at hinner
  apply Complex.ofReal_injective
  push_cast
  exact hinner

/-- The differential energy is literally the Gaussian integral of the squared
weak second derivatives, summed over all ordered coordinate pairs. -/
theorem ginibreDifferentialSecondEnergy_eq_integral {n : ℕ} (hn : 0 < n)
    (g : GinibreFullGradientL2 n) :
    ginibreDifferentialSecondEnergy n hn g =
      ∑ j : Fin n, ∑ k : Fin n, ∫ z,
        Complex.normSq (ginibreDifferentialSecondDerivative n hn g j k z)
          ∂complexGaussianMeasure n := by
  unfold ginibreDifferentialSecondEnergy
  simp_rw [gaussianL2_norm_sq_eq_integral_normSq]

theorem ginibreDifferentialSecondEnergy_eq_tail {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u, g)) :
    ginibreDifferentialSecondEnergy n hn g =
      n * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u)) := by
  obtain ⟨huc, hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  exact (gaussianInverseSquareRootSecondSynthesis_total_energy_modeTail hn
    (ginibreFullCenteredTransform n hn u) (ginibreFullTransformedDbar n hn · g)
    (ginibreFullTransformedDbar_weak_coefficient hn
      (ginibreFullCenter n hn u) g huc hsc)).2

/-- Theorem 1.10: both differential sum-of-squares deficits, with the actual
inverse-square-root vector and its actual weak second Wirtinger derivatives.
All derivative and spectral facts are derived from full generator membership. -/
theorem fullTheoremOneTen {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      (∀ j, IsGaussianWeakDbar n (ginibreDifferentialDeficitVector n hn u.val)
        (ginibreDifferentialFirstDerivative n hn g j) j) ∧
      (∀ j k, IsGaussianWeakDbar n (ginibreDifferentialFirstDerivative n hn g j)
        (ginibreDifferentialSecondDerivative n hn g j k) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      (ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
        ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => a + 2 * (c * coordinateSum z).re) := by
  obtain ⟨g, hu, hs, _, hfirst, hsecond, hequality⟩ := fullTheoremOneNine hn u v hgraph
  obtain ⟨hd, hdd⟩ := ginibreDifferentialDeficit_weak_derivatives hn u.val g hu hs
  have hE := ginibreDifferentialSecondEnergy_eq_tail hn u.val g hu hs
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have h4 : (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g =
      4 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
    rw [hE]
    field_simp
  have h8 : (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g =
      8 * modeTail (positiveHermiteModeMass hn (ginibreFullCenteredTransform n hn u.val)) := by
    rw [hE]
    field_simp
  exact ⟨g, hu, hs, hd, hdd, by rw [h4]; exact hfirst,
    by rw [h8]; exact hsecond, hequality⟩

/-- Theorem 1.10 with literal ordinary Schwartz distributional derivatives. -/
theorem fullTheoremOneTenSchwartz {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val, g) ∧
      (∀ j, IsGaussianSchwartzDbar n (ginibreDifferentialDeficitVector n hn u.val)
        (ginibreDifferentialFirstDerivative n hn g j) j) ∧
      (∀ j k, IsGaussianSchwartzDbar n (ginibreDifferentialFirstDerivative n hn g j)
        (ginibreDifferentialSecondDerivative n hn g j k) k) ∧
      ginibreWeakEnergy n g - 2 * ginibreL2Variance n hn u.val =
        2 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (4 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      ‖v.val‖ ^ 2 - 2 * ginibreWeakEnergy n g =
        ‖v.val + (2 : ℝ) • ginibreFullCenter n hn u.val‖ ^ 2 +
          4 * ‖ginibreFullHolomorphicRemainder n hn u.val‖ ^ 2 +
          (8 / (n : ℝ)) * ginibreDifferentialSecondEnergy n hn g ∧
      (ginibreWeakEnergy n g = 2 * ginibreL2Variance n hn u.val ↔
        ∃ (a : ℝ) (c : ℂ), (u.val : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
          fun z => a + 2 * (c * coordinateSum z).re) := by
  obtain ⟨g, hu, hs, hd, hdd, hfirst, hsecond, heq⟩ := fullTheoremOneTen hn u v hgraph
  exact ⟨g, hu, hs,
    fun j => (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr (hd j),
    fun j k => (gaussianSchwartzDbar_iff_weak hn _ _ k).mpr (hdd j k),
    hfirst, hsecond, heq⟩

end
end GinibrePoincare

#print axioms GinibrePoincare.ginibreDifferentialDeficit_weak_derivatives
#print axioms GinibrePoincare.ginibreDifferentialSecondEnergy_eq_tail
#print axioms GinibrePoincare.ginibreDifferentialSecondEnergy_eq_integral
#print axioms GinibrePoincare.fullTheoremOneTen

#print axioms GinibrePoincare.fullTheoremOneTenSchwartz
