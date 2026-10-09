module
public import GinibrePoincare.Analysis.GaussianClosedFormVolume
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightLocal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section
open MeasureTheory Set Metric
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem complexGaussianMeasure_le_volume_multiple (n : ℕ) (hn : 0 < n) :
    complexGaussianMeasure n ≤ ENNReal.ofReal (((n : ℝ)/Real.pi)^n) • volume := by
  rw [complexGaussianMeasure_eq_real_withDensity hn,← withDensity_const]
  apply withDensity_mono
  exact Filter.Eventually.of_forall (fun z => by
    apply ENNReal.ofReal_le_ofReal
    unfold gaussianLebesgueDensityReal gaussianWeight
    have hs : 0 ≤ configurationNormSq z :=
      Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg _)
    have he : Real.exp (-(n : ℝ)*configurationNormSq z) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (Nat.cast_nonneg n)) hs)
    simpa only [mul_one] using mul_le_mul_of_nonneg_left he
      (pow_nonneg (le_of_lt (div_pos (Nat.cast_pos.mpr hn) Real.pi_pos)) n))

theorem gaussianLp_memLp_local_volume {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (K : Set (Configuration n))
    (hK : IsCompact K) : MemLp u 2 (volume.restrict K) := by
  by_cases hne : K.Nonempty
  · obtain ⟨z, hz, hmin⟩ := hK.exists_isMinOn hne
      (contDiff_gaussianLebesgueDensityReal n).continuous.continuousOn
    let f : Configuration n → ℂ := u
    have hu : MemLp f 2 (complexGaussianMeasure n) := Lp.memLp u
    rw [complexGaussianMeasure_eq_real_withDensity hn] at hu
    exact memLp_restrict_of_weight_lower_bound hK.measurableSet
      (gaussianLebesgueDensityReal_pos hn z) (fun y hy => hmin hy) hu
  · have he : K = ∅ := not_nonempty_iff_eq_empty.mp hne
    simp [he]

/-- Ordinary local L² Dolbeault solvability in complex dimension one on
every open neighborhood. The input has no Gaussian integrability hypothesis.
Closedness of a (0,1)-form in this dimension is automatic. -/
theorem localDolbeault_one_locallyL2 (Ω : Set (Configuration 1)) (hΩ : IsOpen Ω)
    (a : Configuration 1 → ℂ)
    (ha : ∀ K : Set (Configuration 1), IsCompact K → K ⊆ Ω →
      MemLp a 2 (volume.restrict K)) (x : Configuration 1) (hx : x ∈ Ω) :
    ∃ U : Set (Configuration 1), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∃ u : Configuration 1 → ℂ,
        (∀ K : Set (Configuration 1), IsCompact K → MemLp u 2 (volume.restrict K)) ∧
        LocallyIntegrable u volume ∧
        ∀ θ : Configuration 1 → ℂ, ContDiff ℝ 1 θ → HasCompactSupport θ →
          tsupport θ ⊆ U →
          (∫ z, θ z*a z) = -(∫ z, u z*dbarComponent θ 0 z) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let K := closedBall x (r/2)
  let U := ball x (r/2)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ Ω := by
    intro y hy
    apply hball
    have hy' : dist y x ≤ r/2 := hy
    exact lt_of_le_of_lt hy' (by linarith)
  have hU : U ⊆ Ω := ball_subset_closedBall.trans hKU
  have hmvol : MemLp (K.indicator a) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (ha K hK hKU)
  have hm : MemLp (K.indicator a) 2 (complexGaussianMeasure 1) :=
    (hmvol.smul_measure (ENNReal.ofReal_ne_top)).mono_measure
      (complexGaussianMeasure_le_volume_multiple 1 (by decide))
  let A := hm.toLp (K.indicator a)
  have hclosed : IsGaussianVolumeClosedForm 1 (fun _ => A) := by
    intro j k θ hθ hc
    have hjk : j = k := Subsingleton.elim _ _
    rw [hjk]
  obtain ⟨u, _, hdu⟩ := gaussianVolumeClosedFormSolvability (by decide) (fun _ => A) hclosed
  have hAC : volume ≪ complexGaussianMeasure 1 := by
    rw [complexGaussianMeasure_eq_real_withDensity (by decide)]
    apply withDensity_absolutelyContinuous'
      (contDiff_gaussianLebesgueDensityReal 1).continuous.measurable.ennreal_ofReal.aemeasurable
    exact Filter.Eventually.of_forall (fun z =>
      (ENNReal.ofReal_pos.mpr (gaussianLebesgueDensityReal_pos (by decide) z)).ne')
  refine ⟨U, isOpen_ball, mem_ball_self (by linarith), hU, u,
    gaussianLp_memLp_local_volume (by decide) u, (hdu 0).1,?_⟩
  intro θ hθ hc hs
  have he : (∫ z, θ z*a z) = ∫ z, θ z*A z := by
    apply integral_congr_ae
    filter_upwards [hAC.ae_le hm.coeFn_toLp] with z hA
    by_cases hz : z ∈ tsupport θ
    · rw [hA, indicator_of_mem (ball_subset_closedBall (hs hz))]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [he]
  exact (hdu 0).2.2 θ hθ hc

#print axioms complexGaussianMeasure_le_volume_multiple
#print axioms gaussianLp_memLp_local_volume
#print axioms localDolbeault_one_locallyL2
end
end GinibrePoincare
