module

public import GinibrePoincare.Analysis.GaussianBlockRadialLaw
public import GinibrePoincare.Analysis.NonQuadraticRadiusLaw

@[expose] public section

/-! # Actual Euclidean block lifts of the nonquadratic radius laws
The lift uses complex blocks of size `k`, hence real dimension `2k`, and
literal Euclidean volume. No entropy criterion is assumed here.
-/

open MeasureTheory Set
open scoped ENNReal Pointwise
namespace GinibrePoincare
noncomputable section

theorem bakryEmery_volume_squaredBlockRadius (n k : ℕ) (hn : 0 < n) (hk : 0 < k) :
    (volume : Measure (Configuration k)).map (gaussianBlockRadius n k) =
      ((k : ℝ≥0∞) * volume ((gaussianBlockRadius n k) ⁻¹' Iic 1)) • radialPowerMeasure k := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcompact : IsCompact ((gaussianBlockRadius n k) ⁻¹' Iic 1) := by
    apply (isCompact_closedBall (0 : Configuration k) 1).of_isClosed_subset
      (isClosed_le (continuous_gaussianBlockRadius n k) continuous_const)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have hs := configurationNormSq_nonneg x
    have hi : Complex.normSq (x i) ≤ configurationNormSq x :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i)
    change (n : ℝ) * configurationNormSq x ≤ 1 at hx
    rw [Complex.normSq_eq_norm_sq] at hi
    have := norm_nonneg (x i)
    nlinarith
  have hzero : (volume : Measure (Configuration k)) ((gaussianBlockRadius n k) ⁻¹' {0}) = 0 := by
    let : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
    have hs : (gaussianBlockRadius n k) ⁻¹' {0} = {0} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff]
      constructor
      · intro h
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        have hsum : ∑ i, Complex.normSq (x i) = 0 := (mul_eq_zero.mp h).resolve_left hn'
        ext i
        exact Complex.normSq_eq_zero.mp
          ((Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Complex.normSq_nonneg (x j))).mp
            hsum i (Finset.mem_univ i))
      · rintro rfl
        simp [gaussianBlockRadius, configurationNormSq]
    rw [hs]
    exact measure_singleton _
  apply map_quadratic_homogeneous_measure _ _ (continuous_gaussianBlockRadius n k).measurable
    (fun x => mul_nonneg (Nat.cast_nonneg _) (configurationNormSq_nonneg x)) _ hk _ _ hzero
    hcompact.measure_lt_top
  · intro t ht x
    unfold gaussianBlockRadius
    rw [configurationNormSq_real_smul]
    ring
  · intro t ht s
    rw [Measure.addHaar_smul (volume : Measure (Configuration k)) t]
    have hd : Module.finrank ℝ (Configuration k) = 2 * k := by
      simp [Configuration, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
    rw [hd, abs_of_nonneg (pow_nonneg ht.le _)]

/-- Literal unnormalized Euclidean lift in real dimension `2(k+1)`. -/
def bakryEmeryRawBlockLift (n k : ℕ) (V : Potential) : Measure (Configuration (k + 1)) :=
  volume.withDensity (fun x => ENNReal.ofReal
    (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V
      (gaussianBlockRadius 1 (k + 1) x))))

/-- The lift's squared radius has exactly the nonquadratic power-law density
required by Kostlan, up to the explicit unit-ball volume scalar. -/
theorem bakryEmeryRawBlockLift_squaredRadius (n k : ℕ) {V : Potential}
    (hV : Continuous V) :
    (bakryEmeryRawBlockLift n k V).map (gaussianBlockRadius 1 (k + 1)) =
      (((k + 1 : ℕ) : ℝ≥0∞) *
        volume ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1)) •
      rawPotentialSquaredRadiusLaw n k V := by
  unfold bakryEmeryRawBlockLift
  change (volume.withDensity
    ((fun s => ENNReal.ofReal (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s))) ∘
      gaussianBlockRadius 1 (k + 1))).map _ = _
  rw [map_withDensity_comp_measurable _ _
    (continuous_gaussianBlockRadius 1 (k + 1)).measurable
    (fun s => ENNReal.ofReal (Real.exp (-(n : ℝ) * potentialSquaredRadiusProfile V s)))]
  · rw [bakryEmery_volume_squaredBlockRadius 1 (k + 1) (by omega) (by omega),
      withDensity_smul_measure]
    rfl
  · have hp : Continuous (potentialSquaredRadiusProfile V) := by
      unfold potentialSquaredRadiusProfile
      exact hV.comp (Complex.continuous_ofReal.comp Real.continuous_sqrt)
    exact ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp (hp.const_mul (-(n : ℝ)))).measurable

/-- The normalizing mass of the lift is the same explicit scalar times the
actual one-dimensional partition mass. -/
theorem bakryEmeryRawBlockLift_mass (n k : ℕ) {V : Potential}
    (hV : Continuous V) :
    bakryEmeryRawBlockLift n k V univ =
      (((k + 1 : ℕ) : ℝ≥0∞) *
        volume ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1)) *
      rawPotentialSquaredRadiusLaw n k V univ := by
  have h := congrArg (fun μ : Measure ℝ => μ univ)
    (bakryEmeryRawBlockLift_squaredRadius n k hV)
  rw [Measure.map_apply (continuous_gaussianBlockRadius 1 (k + 1)).measurable
    MeasurableSet.univ, preimage_univ, Measure.smul_apply, smul_eq_mul] at h
  exact h

/-- The Euclidean unit-sublevel volume scalar is positive and finite. -/
theorem bakryEmeryBlockScalar_valid (k : ℕ) :
    0 < (((k + 1 : ℕ) : ℝ≥0∞) * volume ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1)) ∧
    (((k + 1 : ℕ) : ℝ≥0∞) * volume ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1)) < ⊤ := by
  have hc : IsCompact ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1) := by
    apply (isCompact_closedBall (0 : Configuration (k + 1)) 1).of_isClosed_subset
      (isClosed_le (continuous_gaussianBlockRadius 1 (k + 1)) continuous_const)
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have hi : Complex.normSq (x i) ≤ configurationNormSq x :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (x j)) (Finset.mem_univ i)
    simp only [gaussianBlockRadius, Nat.cast_one, one_mul] at hx
    change configurationNormSq x ≤ 1 at hx
    rw [Complex.normSq_eq_norm_sq] at hi
    have := norm_nonneg (x i)
    nlinarith
  have hp : 0 < volume ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1) := by
    have ho : IsOpen ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iio 1) :=
      isOpen_Iio.preimage (continuous_gaussianBlockRadius 1 (k + 1))
    have hn : (((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iio 1)).Nonempty := by
      refine ⟨0, ?_⟩
      simp [gaussianBlockRadius, configurationNormSq]
    exact (ho.measure_pos volume hn).trans_le
      (measure_mono (preimage_mono Iio_subset_Iic_self))
  constructor
  · exact ENNReal.mul_pos_iff.mpr ⟨by simp, hp⟩
  · exact ENNReal.mul_lt_top (by simp) hc.measure_lt_top

/-- Normalized Euclidean block lift using its actual partition mass. -/
def bakryEmeryBlockLift (n k : ℕ) (V : Potential) : Measure (Configuration (k + 1)) :=
  (bakryEmeryRawBlockLift n k V univ)⁻¹ • bakryEmeryRawBlockLift n k V

/-- Exact normalized Euclidean lift correspondence, without any assumed
normalizing constants or entropy criterion. -/
theorem bakryEmeryBlockLift_squaredRadius (n k : ℕ) {V : Potential}
    (hV : Continuous V) :
    (bakryEmeryBlockLift n k V).map (gaussianBlockRadius 1 (k + 1)) =
      potentialSquaredRadiusLaw n k V := by
  let b : ℝ≥0∞ := ((k + 1 : ℕ) : ℝ≥0∞) *
    volume ((gaussianBlockRadius 1 (k + 1)) ⁻¹' Iic 1)
  have hb0 : b ≠ 0 := (bakryEmeryBlockScalar_valid k).1.ne'
  have hbt : b ≠ ⊤ := (bakryEmeryBlockScalar_valid k).2.ne
  unfold bakryEmeryBlockLift
  rw [Measure.map_smul _ (continuous_gaussianBlockRadius 1 (k + 1)).measurable.aemeasurable,
    bakryEmeryRawBlockLift_squaredRadius n k hV, bakryEmeryRawBlockLift_mass n k hV,
    smul_smul]
  change ((b * rawPotentialSquaredRadiusLaw n k V univ)⁻¹ * b) • _ = _
  rw [ENNReal.mul_inv, mul_assoc, mul_comm (rawPotentialSquaredRadiusLaw n k V univ)⁻¹ b,
    ← mul_assoc, ENNReal.inv_mul_cancel hb0 hbt, one_mul]
  · rfl
  · exact Or.inl hb0
  · exact Or.inl hbt

/-- Probability validity of every actual lifted coordinate, derived from the
paper's finite partition hypothesis. -/
theorem bakryEmeryBlockLift_isProbabilityMeasure (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (i : Fin n) :
    IsProbabilityMeasure (bakryEmeryBlockLift n i.val V) := by
  have hp := potentialSquaredRadiusLaw_isProbabilityMeasure n hn hV hrot hfin i
  have hm := hp.measure_univ
  rw [← bakryEmeryBlockLift_squaredRadius n i.val hV,
    Measure.map_apply (continuous_gaussianBlockRadius 1 (i.val + 1)).measurable
      MeasurableSet.univ, preimage_univ] at hm
  exact ⟨hm⟩

/-- Actual independent product of Euclidean block lifts. -/
def bakryEmeryProductLift (n : ℕ) (V : Potential) : Measure (GaussianRadialBlocks n) :=
  Measure.pi (fun i : Fin n => bakryEmeryBlockLift n i.val V)

/-- Physical squared radii of the Euclidean block product. -/
def bakryEmeryLiftSquaredRadii (n : ℕ) (x : GaussianRadialBlocks n) : Fin n → ℝ :=
  fun i => gaussianBlockRadius 1 (i.val + 1) (x i)

/-- The normalized lifted product has exactly the actual nonquadratic
independent squared-radius product law. -/
theorem bakryEmeryProductLift_squaredRadii (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) :
    (bakryEmeryProductLift n V).map (bakryEmeryLiftSquaredRadii n) =
      potentialSquaredRadiusProduct n V := by
  have hp : ∀ i : Fin n, IsProbabilityMeasure (bakryEmeryBlockLift n i.val V) :=
    bakryEmeryBlockLift_isProbabilityMeasure n hn hV hrot hfin
  let := hp
  unfold bakryEmeryProductLift bakryEmeryLiftSquaredRadii potentialSquaredRadiusProduct
  rw [Measure.pi_map_pi
    (fun i => (continuous_gaussianBlockRadius 1 (i.val + 1)).measurable.aemeasurable)]
  simp_rw [bakryEmeryBlockLift_squaredRadius n _ hV]

#print axioms bakryEmeryBlockLift_isProbabilityMeasure
#print axioms bakryEmeryProductLift_squaredRadii

#print axioms bakryEmeryBlockScalar_valid
#print axioms bakryEmeryBlockLift_squaredRadius

#print axioms bakryEmeryRawBlockLift_mass

#print axioms bakryEmery_volume_squaredBlockRadius
#print axioms bakryEmeryRawBlockLift_squaredRadius

end
end GinibrePoincare
