module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoung
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

@[expose] public section
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def dolbeaultCompactPairing {n : ℕ} (θ : Configuration n → ℂ)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) : dolbeaultOrdinaryL2 n →L[ℂ] ℂ :=
  innerSL ℂ ((Complex.continuous_conj.comp hθ).memLp_of_hasCompactSupport
    (p := 2) (μ := volume) (hc.comp_left (map_zero _))).toLp

theorem dolbeaultCompactPairing_eq_integral {n : ℕ} (θ : Configuration n → ℂ)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) (u : dolbeaultOrdinaryL2 n) :
    dolbeaultCompactPairing θ hθ hc u = ∫ z : Configuration n, θ z*u z := by
  rw [dolbeaultCompactPairing]
  change inner ℂ _ u = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((Complex.continuous_conj.comp hθ).memLp_of_hasCompactSupport
    (p := 2) (μ := volume) (hc.comp_left (map_zero _))).coeFn_toLp] with z hz
  rw [hz]
  simp [RCLike.inner_apply,mul_comm]

theorem dolbeaultTranslateL2_ae {n : ℕ} (j : Fin n) (y : ℂ) (u : dolbeaultOrdinaryL2 n) :
    (dolbeaultTranslateL2 j y u : Configuration n → ℂ) =ᵐ[volume]
      fun z => u (z-Pi.single j y) :=
  Lp.coeFn_compMeasurePreserving u (dolbeaultCoordinateTranslation_preserving j y)

/-- Literal ordinary-volume compact-test pairing of coordinate convolution.
This needs only L¹ for the kernel and L² for the input. -/
theorem dolbeaultCoordinateConvolution_compact_test {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (u : dolbeaultOrdinaryL2 n)
    (θ : Configuration n → ℂ) (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ z : Configuration n, θ z*(dolbeaultCoordinateConvolution j k u) z) =
      ∫ y : ℂ, k y*(∫ z : Configuration n, θ z*u (z-Pi.single j y)) := by
  rw [← dolbeaultCompactPairing_eq_integral θ hθ hc,
    dolbeaultCoordinateConvolution_pairing j k hk u (dolbeaultCompactPairing θ hθ hc)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    rw [dolbeaultCompactPairing_eq_integral θ hθ hc]
    congr 1
    apply integral_congr_ae
    filter_upwards [dolbeaultTranslateL2_ae j y u] with z hz
    rw [hz])

#print axioms dolbeaultCoordinateConvolution_compact_test
end
end GinibrePoincare
