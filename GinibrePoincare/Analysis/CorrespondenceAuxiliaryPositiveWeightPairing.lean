module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryPositiveWeightLocal

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual ordinary-volume compact test pairing as a continuous functional
on arbitrary positive-local-weight L². -/
def positiveWeightCompactPairing {n : ℕ} (w : Configuration n → ℝ)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (φ : Configuration n → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z))) →L[ℝ] ℂ := by
  let c := Classical.choose (hw (tsupport φ) hc)
  have hcw := Classical.choose_spec (hw (tsupport φ) hc)
  let R := positiveWeightLocalRestriction volume w (isClosed_tsupport φ).measurableSet hcw.1 hcw.2
  let hm := ((Complex.continuous_conj.comp hφ).memLp_of_hasCompactSupport (p := 2) (μ := volume)
    (hc.comp_left (map_zero _))).restrict (tsupport φ)
  let g := hm.toLp (conj ∘ φ)
  exact ((innerSL ℂ g).restrictScalars ℝ).comp R

theorem positiveWeightCompactPairing_eq_integral {n : ℕ} (w : Configuration n → ℝ)
    (hw : ∀ K : Set (Configuration n), IsCompact K →
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ K, c ≤ w z)
    (φ : Configuration n → ℂ) (hφ : Continuous φ) (hc : HasCompactSupport φ)
    (u : Lp ℂ 2 (volume.withDensity (fun z => ENNReal.ofReal (w z)))) :
    positiveWeightCompactPairing w hw φ hφ hc u = ∫ z, φ z * u z := by
  let c := Classical.choose (hw (tsupport φ) hc)
  have hcw := Classical.choose_spec (hw (tsupport φ) hc)
  let R := positiveWeightLocalRestriction volume w (isClosed_tsupport φ).measurableSet hcw.1 hcw.2
  let hm := ((Complex.continuous_conj.comp hφ).memLp_of_hasCompactSupport (p := 2) (μ := volume)
    (hc.comp_left (map_zero _))).restrict (tsupport φ)
  let g := hm.toLp (conj ∘ φ)
  change inner ℂ g (R u) = _
  rw [L2.inner_def]
  have he : (∫ z in tsupport φ, inner ℂ (g z) ((R u) z)) =
      ∫ z in tsupport φ, φ z * u z := by
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp, positiveWeightLocalRestriction_coe volume w
      (isClosed_tsupport φ).measurableSet hcw.1 hcw.2 u] with z hg hr
    rw [hg, hr]
    simp [RCLike.inner_apply, mul_comm]
  rw [he]
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  rw [image_eq_zero_of_notMem_tsupport hz, zero_mul]

#print axioms positiveWeightCompactPairing_eq_integral
end
end GinibrePoincare
