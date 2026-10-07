module

public import GinibrePoincare.Analysis.NonQuadraticRadiusLaw
public import GinibrePoincare.Analysis.RadialGradientTransfer

@[expose] public section

/-! # Exact nonquadratic radial gradient transfer
The derivative calculation is independent of confinement. Combining it with
the actual general Kostlan law transports the Euclidean energy exactly.
-/
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- Unscaled squared individual radii. -/
def potentialSquaredRadii (n : ℕ) (z : Configuration n) : Fin n → ℝ :=
  fun i => Complex.normSq (z i)

/-- Their actual real Fréchet derivative. -/
def potentialSquaredRadiiDerivative (n : ℕ) (z : Configuration n) :
    Configuration n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    (2 * (z i).re) • (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    (2 * (z i).im) • (Complex.imCLM.comp (ContinuousLinearMap.proj i)))

theorem hasFDerivAt_potentialSquaredRadii (n : ℕ) (z : Configuration n) :
    HasFDerivAt (potentialSquaredRadii n) (potentialSquaredRadiiDerivative n z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hr := Complex.reCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have h := (hr.mul hr).add (hi.mul hi)
  convert! h using 1
  ext v
  simp
  ring

private theorem potentialSquaredRadiiDerivative_real (n : ℕ) (z : Configuration n) (i : Fin n) :
    potentialSquaredRadiiDerivative n z (realCoordinateDirection i) =
      (2 * (z i).re) • (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [potentialSquaredRadiiDerivative, realCoordinateDirection, coordinateDirection]
  · simp [potentialSquaredRadiiDerivative, realCoordinateDirection, coordinateDirection, h]

private theorem potentialSquaredRadiiDerivative_imag (n : ℕ) (z : Configuration n) (i : Fin n) :
    potentialSquaredRadiiDerivative n z (imaginaryCoordinateDirection i) =
      (2 * (z i).im) • (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [potentialSquaredRadiiDerivative, imaginaryCoordinateDirection, coordinateDirection]
  · simp [potentialSquaredRadiiDerivative, imaginaryCoordinateDirection, coordinateDirection, h]

/-- Literal unscaled squared-radius chain rule, including at zero coordinates. -/
theorem realGradientNormSq_potentialSquaredRadii (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (z : Configuration n) :
    realGradientNormSq (fun z => F (potentialSquaredRadii n z)) z =
      gammaRadialEnergyDensity F (potentialSquaredRadii n z) := by
  have hd := ((hF _).hasFDerivAt.comp z (hasFDerivAt_potentialSquaredRadii n z)).fderiv
  unfold realGradientNormSq
  change fderiv ℝ (fun z => F (potentialSquaredRadii n z)) z = _ at hd
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, potentialSquaredRadiiDerivative_real,
    potentialSquaredRadiiDerivative_imag, map_smul, smul_eq_mul]
  unfold gammaRadialEnergyDensity radiusPartial potentialSquaredRadii
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Complex.normSq_apply]
  ring

/-- The full Euclidean gradient energy is exactly the independent-radius
weighted energy, for any smooth compact symmetric radius profile. -/
theorem potentialGradientEnergy_radial_eq_product (n : ℕ) (hn : 0 < n) {V : Potential}
    (hVc : Continuous V) (hVr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ ∞ F)
    (hc : HasCompactSupport F) (hS : IsSymmetricRadiusTest n F) :
    potentialGradientEnergy n V (fun z => F (potentialSquaredRadii n z)) =
      ∫ r, gammaRadialEnergyDensity F r ∂potentialSquaredRadiusProduct n V := by
  have hd := hF.differentiable (by simp)
  obtain ⟨hcont, hcomp⟩ := gammaRadialEnergyDensity_regular F hF hc
  obtain ⟨C, hC⟩ := hcomp.exists_bound_of_continuous hcont
  have ht := potential_radial_expectation_eq_squaredRadiusProduct n hn hVc hVr hfin
    (gammaRadialEnergyDensity F) hcont (gammaRadialEnergyDensity_symmetric F hd hS) C hC
  unfold potentialGradientEnergy
  simp_rw [realGradientNormSq_potentialSquaredRadii n F hd]
  exact ht

#print axioms realGradientNormSq_potentialSquaredRadii
#print axioms potentialGradientEnergy_radial_eq_product
end
end GinibrePoincare
