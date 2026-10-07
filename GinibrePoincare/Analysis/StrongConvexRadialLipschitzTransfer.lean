module

public import GinibrePoincare.Analysis.StrongConvexRadialSymmetrizedLaw
public import GinibrePoincare.Analysis.StrongConvexRadialProductLipschitzLSI
public import GinibrePoincare.Analysis.StrongConvexRadialGradientTransfer

@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem radius_relabel_volume_preserving (n : ℕ) (e : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun r : Fin n → ℝ => r ∘ e) volume volume := by
  convert volume_measurePreserving_piCongrLeft (fun _ : Fin n => ℝ) e.symm using 1
  ext r i
  simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem rhoConvex_magnitude_map_absolutelyContinuous (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hfin : potentialPartition n V < ⊤) :
    (potentialMeasure n V).map magnitudeVector ≪ volume := by
  classical
  rw [potential_magnitude_map_eq_symmetrizedRadiusProduct n hn hV.continuous hrot hfin]
  have ha := rhoConvex_radiusProduct_absolutelyContinuous n hn ρ hρ hV hrot hc
  have hb (e : Equiv.Perm (Fin n)) :
      (potentialRadiusProduct n V).map (fun r => r ∘ e) ≪ volume := by
    have hh := ha.map (radius_relabel_volume_preserving n e).measurable
    rwa [(radius_relabel_volume_preserving n e).map_eq] at hh
  intro s hs
  simp only [potentialSymmetrizedRadiusProduct, Measure.smul_apply,
    Measure.finsetSum_apply, hb _ hs, Finset.sum_const_zero, smul_zero]

/-- Rademacher differentiability at the actual magnitudes under the interacting gas. -/
theorem rhoConvex_radial_profile_differentiableAt_ae (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F) :
    ∀ᵐ z ∂potentialMeasure n V, DifferentiableAt ℝ F (magnitudeVector z) := by
  have ha := (rhoConvex_magnitude_map_absolutelyContinuous n hn ρ hρ hV hrot hc hfin).ae_le
    (hF.ae_differentiableAt (μ := volume))
  have hm : Measurable (magnitudeVector : Configuration n → Fin n → ℝ) :=
    Measurable.of_eval (fun i => (measurable_pi_apply i).norm)
  exact ae_of_ae_map hm.aemeasurable ha
private theorem radialLipschitzDerivative_direction {n : ℕ} (z : Configuration n)
    (i : Fin n) (w : ℂ) :
    magnitudeDerivative z (coordinateDirection i w) =
      (((z i).re * w.re + (z i).im * w.im) / ‖z i‖) •
        (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [magnitudeDerivative, coordinateDirection]
    ring
  · simp [magnitudeDerivative, coordinateDirection, hj]

theorem realGradientNormSq_magnitude_at {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (z : Configuration n) (hF : DifferentiableAt ℝ F (magnitudeVector z)) (hz : ∀ i, z i ≠ 0) :
    realGradientNormSq (fun z => F (magnitudeVector z)) z =
      magnitudeEnergyDensity F (magnitudeVector z) := by
  have hd := (hF.hasFDerivAt.comp z (hasFDerivAt_magnitudeVector z hz)).fderiv
  change fderiv ℝ (fun z => F (magnitudeVector z)) z = _ at hd
  unfold realGradientNormSq
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, realCoordinateDirection,
    imaginaryCoordinateDirection, radialLipschitzDerivative_direction, map_smul, smul_eq_mul,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    add_zero, zero_add]
  unfold magnitudeEnergyDensity radiusPartial
  apply Finset.sum_congr rfl
  intro i hi
  have hn : ‖z i‖ ≠ 0 := norm_ne_zero_iff.mpr (hz i)
  have hs : (z i).re ^ 2 + (z i).im ^ 2 = ‖z i‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq (z i)
  field_simp
  nlinarith [hs]

theorem rhoConvex_realGradientNormSq_magnitude_lipschitz_ae (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (hfin : potentialPartition n V < ⊤)
    (F : (Fin n → ℝ) → ℝ) {K : ℝ≥0} (hF : LipschitzWith K F) :
    (fun z => realGradientNormSq (fun z => F (magnitudeVector z)) z) =ᵐ[potentialMeasure n V]
      (fun z => magnitudeEnergyDensity F (magnitudeVector z)) := by
  filter_upwards [rhoConvex_radial_profile_differentiableAt_ae n hn ρ hρ hV hrot hc hfin F hF,
    potential_coordinates_ne_zero_ae n V] with z hz hz0
  exact realGradientNormSq_magnitude_at F z hz hz0

def radialPermutationCLM {n : ℕ} (e : Equiv.Perm (Fin n)) :
    (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj (e i))

theorem radiusPartial_permutation_unconditional {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hs : IsSymmetricRadiusTest n F) (e : Equiv.Perm (Fin n)) (r : Fin n → ℝ) (i : Fin n) :
    radiusPartial F (r ∘ e) i = radiusPartial F r (e i) := by
  have heq : F ∘ radialPermutationCLM e = F := funext (hs e)
  by_cases hd : DifferentiableAt ℝ F (r ∘ e)
  · have hh := (hd.hasFDerivAt.comp r (radialPermutationCLM e).hasFDerivAt).fderiv
    rw [heq] at hh
    have hv := congrArg (fun L : (Fin n → ℝ) →L[ℝ] ℝ => L (Pi.single (e i) 1)) hh
    have he : radialPermutationCLM e (Pi.single (e i) 1) = (Pi.single i 1 : Fin n → ℝ) := by
      ext j
      simp [radialPermutationCLM, Pi.single_apply, e.injective.eq_iff]
    simp only [ContinuousLinearMap.comp_apply] at hv
    rw [he] at hv
    exact hv.symm
  · have hr : ¬ DifferentiableAt ℝ F r := by
      intro hh
      have hx : radialPermutationCLM e.symm (r ∘ e) = r := by ext j; simp [radialPermutationCLM]
      have hh' := (hx.symm ▸ hh).comp (r ∘ e) (radialPermutationCLM e.symm).differentiableAt
      have hi : F ∘ radialPermutationCLM e.symm = F := funext (hs e.symm)
      rw [hi] at hh'
      exact hd hh'
    simp [radiusPartial, fderiv_zero_of_not_differentiableAt hd,
      fderiv_zero_of_not_differentiableAt hr]

theorem magnitudeEnergyDensity_symmetric_unconditional {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hs : IsSymmetricRadiusTest n F) : IsSymmetricRadiusTest n (magnitudeEnergyDensity F) := by
  intro e r
  unfold magnitudeEnergyDensity
  simp only [radiusPartial_permutation_unconditional F hs e r]
  exact Equiv.sum_comp e (fun i => radiusPartial F r i ^ 2)


#print axioms rhoConvex_realGradientNormSq_magnitude_lipschitz_ae
#print axioms magnitudeEnergyDensity_symmetric_unconditional
end
end GinibrePoincare
