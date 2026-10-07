module

public import GinibrePoincare.Analysis.GinibreEntireProjectionGeometry
public import GinibrePoincare.Analysis.GaussianEntireSpaceClosure
public import GinibrePoincare.Analysis.GinibreComplexProjectionGeometry

@[expose] public section

/-! # Ambient entire projections under the Vandermonde isometry -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

theorem normalizedVandermonde_holomorphicAmbient_mem_zeroMode {n : ℕ} (hn : 0 < n)
    (y : Lp ℂ 2 (ginibreMeasure n)) (hy : y ∈ ginibreHolomorphicAmbientClosedSpan n hn) :
    normalizedVandermondeL2 n hn y ∈ hermiteAntiDegreeClosedSpan n hn 0 := by
  obtain ⟨s, hs, rfl⟩ := hy
  let U := vandermondeSymmetricAlternatingEquiv n hn
  have him : U s ∈ (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
      U.toLinearMap := ⟨s, hs, rfl⟩
  rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan] at him
  exact gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn him

/-- The ambient Gaussian entire projection of an alternating transform is
exactly the transform of the ambient Ginibre holomorphic projection. -/
theorem normalizedVandermonde_holomorphicProjection {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    normalizedVandermondeL2 n hn
      ((ginibreHolomorphicAmbientClosedSpan n hn).starProjection u.val) =
      (gaussianEntireClosedSpace n hn).starProjection (normalizedVandermondeL2 n hn u.val) := by
  let T := normalizedVandermondeL2 n hn
  let U := vandermondeSymmetricAlternatingEquiv n hn
  let w := T u.val
  have hw : w ∈ gaussianAlternatingL2 n := (U u).property
  let a : gaussianAlternatingL2 n :=
    ⟨gaussianHermiteMode hn 0 w, gaussianHermiteMode_mem_alternating hn 0 hw⟩
  have ha : a ∈ gaussianAlternatingZeroModeClosedSpan n hn := by
    change a ∈ (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
    rw [gaussianAlternatingZeroModeClosedSpan_eq_hermiteZeroMode_comap]
    change gaussianHermiteMode hn 0 w ∈ hermiteAntiDegreeClosedSpan n hn 0
    rw [gaussianHermiteMode_eq_antiDegreeProjection]
    exact Submodule.starProjection_apply_mem _ w
  have him : a ∈ (ginibreSymmetricHolomorphicPolynomialClosedSpan n hn).toSubmodule.map
      U.toLinearMap := by
    rw [map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
    exact ha
  obtain ⟨h, hh, hUa⟩ := him
  change U h = a at hUa
  have hT : T h.val = gaussianHermiteMode hn 0 w := by
    change (U h).val = a.val
    rw [hUa]
  have hH : h.val ∈ ginibreHolomorphicAmbientClosedSpan n hn := ⟨h, hh, rfl⟩
  have hp : (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u.val = h.val := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hH
    intro y hy
    have hTy := normalizedVandermonde_holomorphicAmbient_mem_zeroMode hn y hy
    have ho := Submodule.starProjection_inner_eq_zero w (T y) hTy
    change inner ℂ (w-hermiteAntiDegreeProjection n hn 0 w) (T y) = 0 at ho
    rw [← gaussianHermiteMode_eq_antiDegreeProjection] at ho
    calc
      inner ℂ (u.val-h.val) y = inner ℂ (T (u.val-h.val)) (T y) :=
        (T.inner_map_map (u.val-h.val) y).symm
      _ = inner ℂ (w-gaussianHermiteMode hn 0 w) (T y) := by rw [map_sub, hT]
      _ = 0 := ho
  rw [hp, gaussianEntireProjection_eq_zeroMode]
  exact hT

/-- Normalized representative distance transport at the level of actual
ambient orthogonal projections. -/
theorem normalizedVandermonde_projection_distance {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ‖normalizedVandermondeL2 n hn u.val -
      (gaussianEntireClosedSpace n hn).starProjection (normalizedVandermondeL2 n hn u.val)‖ ^ 2 =
      ‖u.val - (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u.val‖ ^ 2 := by
  rw [← normalizedVandermonde_holomorphicProjection hn u, ← map_sub,
    (normalizedVandermondeL2 n hn).norm_map]

/-- Lemma 2.6's distance transport for actual entire closed subspaces. -/
theorem normalizedVandermonde_entire_infDist {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    Metric.infDist (normalizedVandermondeL2 n hn u.val)
      (gaussianEntireClosedSpace n hn : Set (Lp ℂ 2 (complexGaussianMeasure n))) ^ 2 =
      Metric.infDist u.val
        (ginibreDivisibleEntireClosedSpace n hn : Set (Lp ℂ 2 (ginibreMeasure n))) ^ 2 := by
  rw [closedSubspace_infDist_eq_projectionNorm, closedSubspace_infDist_eq_projectionNorm,
    ginibreDivisibleEntireClosedSpace_eq_holomorphic]
  exact normalizedVandermonde_projection_distance hn u

/-- The unnormalized form (2.23) has exactly the paper's Gaussian
Vandermonde normalizing mass c'_n, rather than a silently normalized coefficient. -/
theorem vandermonde_entire_infDist {n : ℕ} (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    Metric.infDist ((groundStateNormalization n : ℂ) • normalizedVandermondeL2 n hn u.val)
      (gaussianEntireClosedSpace n hn : Set (Lp ℂ 2 (complexGaussianMeasure n))) ^ 2 =
      (ginibreNormalizingMass n).toReal * Metric.infDist u.val
        (ginibreDivisibleEntireClosedSpace n hn : Set (Lp ℂ 2 (ginibreMeasure n))) ^ 2 := by
  rw [closedSubspace_infDist_eq_projectionNorm, map_smul, ← smul_sub, norm_smul, mul_pow,
    Complex.norm_real, Real.norm_eq_abs]
  rw [groundStateNormalization, abs_of_nonneg (Real.sqrt_nonneg _),
    Real.sq_sqrt ENNReal.toReal_nonneg]
  rw [← closedSubspace_infDist_eq_projectionNorm]
  rw [normalizedVandermonde_entire_infDist hn u]

end
end GinibrePoincare
#print axioms GinibrePoincare.normalizedVandermonde_holomorphicProjection
#print axioms GinibrePoincare.normalizedVandermonde_projection_distance

#print axioms GinibrePoincare.vandermonde_entire_infDist
