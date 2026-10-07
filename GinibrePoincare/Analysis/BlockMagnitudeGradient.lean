module

public import GinibrePoincare.Analysis.MagnitudeNullSets

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

def blockMagnitudeDerivative (n : ℕ) (x : GaussianRadialBlocks n) :
    GaussianRadialBlocks n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => (blockMagnitudes n x i)⁻¹ •
    ∑ j : Fin (i.val + 1), ((x i j).re • (Complex.reCLM.comp (blockCoordinateProjection n i j)) +
      (x i j).im • (Complex.imCLM.comp (blockCoordinateProjection n i j))))

theorem hasFDerivAt_blockMagnitudes (n : ℕ) (hn : 0 < n) (x : GaussianRadialBlocks n)
    (hx : ∀ i, 0 < blockMagnitudes n x i) :
    HasFDerivAt (blockMagnitudes n) (blockMagnitudeDerivative n x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hd := (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp x
    (hasFDerivAt_blockRadii n x)
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hs : configurationNormSq (x i) ≠ 0 := by
    intro hs
    have hh := hx i
    simp [blockMagnitudes, gaussianBlockMagnitude, hs] at hh
  have h := (hd.const_mul (n : ℝ)⁻¹).sqrt (by
    simpa [gaussianBlockRadii, gaussianBlockRadius, hnR] using hs)
  convert! h using 1
  · funext y
    simp [blockMagnitudes, gaussianBlockMagnitude, gaussianBlockRadii, gaussianBlockRadius, hnR]
  · ext v
    simp [blockRadiusDerivative, blockCoordinateProjection,
      gaussianBlockRadii, gaussianBlockRadius, blockMagnitudes, gaussianBlockMagnitude,
      hnR, Finset.mul_sum]
    field_simp

private theorem blockMagnitudeDerivative_direction (n : ℕ) (x : GaussianRadialBlocks n)
    (i : Fin n) (j : Fin (i.val + 1)) (w : ℂ) :
    blockMagnitudeDerivative n x (Pi.single i (coordinateDirection j w)) =
      (((x i j).re * w.re + (x i j).im * w.im) / blockMagnitudes n x i) •
        (Pi.single i 1 : Fin n → ℝ) := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [blockMagnitudeDerivative, blockCoordinateProjection, coordinateDirection]
    rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b hb hbj
      simp [hbj]
    · intro h
      simp at h
  · simp [blockMagnitudeDerivative, blockCoordinateProjection, hk]

/-- The norm lift preserves magnitude-coordinate gradient energy almost everywhere. -/
theorem blockGradientNormSq_magnitude (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Differentiable ℝ F)
    (x : GaussianRadialBlocks n) (hx : ∀ i, 0 < blockMagnitudes n x i) :
    blockGradientNormSq (fun x => F (blockMagnitudes n x)) x =
      magnitudeEnergyDensity F (blockMagnitudes n x) := by
  have hd := ((hF _).hasFDerivAt.comp x (hasFDerivAt_blockMagnitudes n hn x hx)).fderiv
  change fderiv ℝ (fun x => F (blockMagnitudes n x)) x = _ at hd
  unfold blockGradientNormSq
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, realCoordinateDirection,
    imaginaryCoordinateDirection, blockMagnitudeDerivative_direction, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
    map_smul, smul_eq_mul]
  unfold magnitudeEnergyDensity radiusPartial
  apply Finset.sum_congr rfl
  intro i hi
  let a := fderiv ℝ F (blockMagnitudes n x) (Pi.single i 1)
  let b := blockMagnitudes n x i
  have hb : b ≠ 0 := (hx i).ne'
  have hsum : ∑ j : Fin (i.val + 1), ((x i j).re ^ 2 + (x i j).im ^ 2) = b ^ 2 := by
    dsimp [b, blockMagnitudes, gaussianBlockMagnitude]
    rw [Real.sq_sqrt (configurationNormSq_nonneg (x i))]
    unfold configurationNormSq
    apply Finset.sum_congr rfl
    intro j hj
    simp [Complex.normSq_apply, pow_two]
  change (∑ j : Fin (i.val + 1), (((x i j).re / b * a) ^ 2 + ((x i j).im / b * a) ^ 2)) = a ^ 2
  calc
    _ = (∑ j : Fin (i.val + 1), ((x i j).re ^ 2 + (x i j).im ^ 2)) * a ^ 2 / b ^ 2 := by
      rw [Finset.sum_mul, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by rw [hsum]; field_simp

end
end GinibrePoincare
