module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultLpBall
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Ordinary local Dolbeault exactness for distributionally closed locally
L² (0,1)-forms in every complex dimension and on arbitrary open neighborhoods.
The source has no global integrability or Gaussian-weight assumptions.
The compact localization and bounded coordinate homotopy are constructed
internally; the resulting primitive is ordinary L² globally. -/
theorem localDolbeault_locallyL2 {n : ℕ}
    (Ω : Set (Configuration n)) (hΩ : IsOpen Ω)
    (α : Fin n → Configuration n → ℂ)
    (hα : ∀ j K, IsCompact K → K ⊆ Ω → MemLp (α j) 2 (volume.restrict K))
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ω → ∀ j k,
        (∫ y, dbarComponent θ k y*α j y) = ∫ y, dbarComponent θ j y*α k y)
    (x : Configuration n) (hx : x ∈ Ω) :
    ∃ U : Set (Configuration n), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∃ u : dolbeaultOrdinaryL2 n, ∀ θ : Configuration n → ℂ,
        ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ U → ∀ j,
          (∫ p, θ p*α j p) = -(∫ p, dbarComponent θ j p*u p) := by
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hΩ x hx
  let R := r/2
  have hR : 0 < R := half_pos hr
  let K := closedBall x R
  have hK : IsCompact K := isCompact_closedBall x R
  have hKΩ : K ⊆ Ω := (closedBall_subset_ball (by change r/2 < r; linarith)).trans hball
  let A : Fin n → Configuration n → ℂ := fun j => K.indicator (α j)
  have hA (j : Fin n) : MemLp (A j) 2 volume :=
    (memLp_indicator_iff_restrict hK.measurableSet).mpr (hα j K hK hKΩ)
  have hcA (j : Fin n) : HasCompactSupport (A j) := by
    apply HasCompactSupport.of_support_subset_isCompact hK
    intro p hp
    by_contra hpK
    exact hp (indicator_of_notMem hpK _)
  have hclosedA (θ : Configuration n → ℂ) (hθ : ContDiff ℝ ∞ θ)
      (hc : HasCompactSupport θ) (hs : tsupport θ ⊆ ball x R) (j k : Fin n) :
      (∫ y, dbarComponent θ k y*A j y) = ∫ y, dbarComponent θ j y*A k y :=
    localDolbeault_indicator_closed Ω α hclosed x R hKΩ θ hθ hc hs j k
  obtain ⟨U,hU,hxU,hUb,u,hsol⟩ := localDolbeault_compactLp_ball A hA hcA x R hR hclosedA
  refine ⟨U,hU,hxU,hUb.trans (ball_subset_closedBall.trans hKΩ),u,?_⟩
  intro θ hθ hc hs j
  have he (p : Configuration n) : θ p*A j p = θ p*α j p := by
    by_cases hp : p ∈ tsupport θ
    · have hpK : p ∈ K := ball_subset_closedBall (hUb (hs hp))
      rw [show A j p = α j p from indicator_of_mem hpK _]
    · rw [image_eq_zero_of_notMem_tsupport hp,zero_mul,zero_mul]
  have hl : (∫ p, θ p*A j p) = ∫ p, θ p*α j p := by
    apply integral_congr_ae
    exact ae_of_all _ he
  have ht := hsol θ hθ hc hs j
  rw [hl] at ht
  exact ht

/-- Function-valued ordinary local L² primitive, with the full compact-test
distributional equation on a genuine smaller open neighborhood. -/
theorem localDolbeault_locallyL2_representative {n : ℕ}
    (Ω : Set (Configuration n)) (hΩ : IsOpen Ω)
    (α : Fin n → Configuration n → ℂ)
    (hα : ∀ j K, IsCompact K → K ⊆ Ω → MemLp (α j) 2 (volume.restrict K))
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ Ω → ∀ j k,
        (∫ y, dbarComponent θ k y*α j y) = ∫ y, dbarComponent θ j y*α k y)
    (x : Configuration n) (hx : x ∈ Ω) :
    ∃ U : Set (Configuration n), IsOpen U ∧ x ∈ U ∧ U ⊆ Ω ∧
      ∃ u : Configuration n → ℂ, MemLp u 2 volume ∧ LocallyIntegrable u volume ∧
        (∀ K, IsCompact K → K ⊆ U → MemLp u 2 (volume.restrict K)) ∧
        ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
          tsupport θ ⊆ U → ∀ j,
            (∫ p, θ p*α j p) = -(∫ p, dbarComponent θ j p*u p) := by
  obtain ⟨U,hU,hxU,hUΩ,u,hsol⟩ := localDolbeault_locallyL2 Ω hΩ α hα hclosed x hx
  have hu := Lp.memLp u
  exact ⟨U,hU,hxU,hUΩ,u,hu,hu.locallyIntegrable (by norm_num),
    fun K _ _ => hu.mono_measure Measure.restrict_le_self,hsol⟩

#print axioms localDolbeault_locallyL2
#print axioms localDolbeault_locallyL2_representative
end
end GinibrePoincare
