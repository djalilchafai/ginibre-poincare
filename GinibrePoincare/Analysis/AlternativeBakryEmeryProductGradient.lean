module

public import GinibrePoincare.Analysis.AlternativeBakryEmeryLiftTransfer
public import GinibrePoincare.Analysis.NonQuadraticGradientTransfer
public import GinibrePoincare.Analysis.GaussianRadialLift

@[expose] public section

/-! # Ordinary Euclidean energy of the nonquadratic block-product lift -/

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

def bakryEmeryLiftRadiusDerivative (n : ℕ) (x : GaussianRadialBlocks n) :
    GaussianRadialBlocks n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ∑ j : Fin (i.val + 1),
    ((2 * (x i j).re) •
      (Complex.reCLM.comp (blockCoordinateProjection n i j)) +
    (2 * (x i j).im) •
      (Complex.imCLM.comp (blockCoordinateProjection n i j))))

theorem hasFDerivAt_bakryEmeryLiftSquaredRadii (n : ℕ) (x : GaussianRadialBlocks n) :
    HasFDerivAt (bakryEmeryLiftSquaredRadii n) (bakryEmeryLiftRadiusDerivative n x) x := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hd (j : Fin (i.val + 1)) :
      HasFDerivAt (fun y : GaussianRadialBlocks n => Complex.normSq (y i j))
        ((2 * (x i j).re) •
          (Complex.reCLM.comp (blockCoordinateProjection n i j)) +
         (2 * (x i j).im) •
          (Complex.imCLM.comp (blockCoordinateProjection n i j))) x := by
    have hr := Complex.reCLM.hasFDerivAt.comp x
      (blockCoordinateProjection n i j).hasFDerivAt
    have hi := Complex.imCLM.hasFDerivAt.comp x
      (blockCoordinateProjection n i j).hasFDerivAt
    have h := ((hr.mul hr).add (hi.mul hi))
    convert! h using 1
    ext v
    simp [blockCoordinateProjection]
    ring
  have h := HasFDerivAt.sum (u := Finset.univ) (fun j _ => hd j)
  convert! h using 1
  funext y
  simp [bakryEmeryLiftSquaredRadii, gaussianBlockRadius, configurationNormSq, Nat.cast_one, one_mul, Finset.mul_sum]

private theorem bakryEmeryLiftRadiusDerivative_direction (n : ℕ) (x : GaussianRadialBlocks n)
    (i : Fin n) (j : Fin (i.val + 1)) (w : ℂ) :
    bakryEmeryLiftRadiusDerivative n x (Pi.single i (coordinateDirection j w)) =
      (2 * ((x i j).re * w.re + (x i j).im * w.im)) •
        (Pi.single i 1 : Fin n → ℝ) := by
  ext k
  by_cases hk : k = i
  · subst k
    simp [bakryEmeryLiftRadiusDerivative, blockCoordinateProjection, coordinateDirection]
    rw [Finset.sum_eq_single j]
    · simp
      ring
    · intro b hb hbj
      simp [hbj]
    · intro h
      simp at h
  · simp [bakryEmeryLiftRadiusDerivative, blockCoordinateProjection, hk]

/-- The Gaussian lift has exactly the same Gamma-coordinate gradient density. -/
theorem bakryEmeryProductLift_gradient_norm_sq (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (x : GaussianRadialBlocks n) :
    blockGradientNormSq (fun x => F (bakryEmeryLiftSquaredRadii n x)) x =
      gammaRadialEnergyDensity F (bakryEmeryLiftSquaredRadii n x) := by
  have hd := ((hF _).hasFDerivAt.comp x (hasFDerivAt_bakryEmeryLiftSquaredRadii n x)).fderiv
  change fderiv ℝ (fun x => F (bakryEmeryLiftSquaredRadii n x)) x = _ at hd
  unfold blockGradientNormSq
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, realCoordinateDirection,
    imaginaryCoordinateDirection, bakryEmeryLiftRadiusDerivative_direction, Complex.one_re,
    Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
    map_smul, smul_eq_mul]
  unfold gammaRadialEnergyDensity radiusPartial
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  unfold bakryEmeryLiftSquaredRadii gaussianBlockRadius configurationNormSq
  simp only [Nat.cast_one, one_mul]
  rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Complex.normSq_apply]
  ring


/-- Exact integrated Euclidean gradient energy under the actual product lift. -/
theorem bakryEmeryProductLift_energy (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (∫ x, blockGradientNormSq (fun y => F (bakryEmeryLiftSquaredRadii n y)) x
      ∂bakryEmeryProductLift n V) =
      ∫ r, gammaRadialEnergyDensity F r ∂potentialSquaredRadiusProduct n V := by
  simp_rw [bakryEmeryProductLift_gradient_norm_sq n F (hF.differentiable (by simp))]
  rw [← bakryEmeryProductLift_squaredRadii n hn hV hrot hfin]
  exact (integral_map (continuous_bakryEmeryLiftSquaredRadii n).measurable.aemeasurable
    (gammaRadialEnergyDensity_regular F hF hc).1.aestronglyMeasurable).symm

/-- The interacting gas and its actual Euclidean lift have equal ordinary
Euclidean Dirichlet energies. -/
theorem bakryEmery_potential_energy_eq_lift (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (hs : IsSymmetricRadiusTest n F) :
    potentialGradientEnergy n V (fun z => F (potentialSquaredRadii n z)) =
      ∫ x, blockGradientNormSq (fun y => F (bakryEmeryLiftSquaredRadii n y)) x
        ∂bakryEmeryProductLift n V := by
  rw [potentialGradientEnergy_radial_eq_product n hn hV hrot hfin F hF hc hs,
    bakryEmeryProductLift_energy n hn hV hrot hfin F hF hc]

#print axioms bakryEmeryProductLift_energy
#print axioms bakryEmery_potential_energy_eq_lift

#print axioms hasFDerivAt_bakryEmeryLiftSquaredRadii
#print axioms bakryEmeryProductLift_gradient_norm_sq

end
end GinibrePoincare
