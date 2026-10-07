module

public import GinibrePoincare.Analysis.NonQuadraticLpMultiplier
public import GinibrePoincare.Analysis.NonQuadraticComplexTestInverse
public import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

/-! # Genuine local L² continuity of weighted compact translations -/
open MeasureTheory Filter
open scoped Topology Pointwise ContDiff ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
local instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

def planarWeightedTranslateFunction (n : ℕ) (V : ℂ → ℝ) (ψ : ℂ → ℂ) (a x : ℂ) :=
  ψ (x - a) * planarPotentialHalfWeight n V x

theorem planarWeightedTranslate_memLp (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a : ℂ) :
    MemLp (planarWeightedTranslateFunction n V ψ a) 2 volume := by
  have hw : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  have hs : HasCompactSupport (fun x => ψ (x - a)) := by
    simpa only [sub_eq_add_neg, Function.comp_def, Homeomorph.coe_addRight] using hc.comp_homeomorph (Homeomorph.addRight (-a))
  exact ((hψ.comp (continuous_id.sub continuous_const)).mul hw).memLp_of_hasCompactSupport hs.mul_right

def planarWeightedTranslateL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (a : ℂ) : PlanarLebesgueL2 :=
  (planarWeightedTranslate_memLp n V hV ψ hψ hc a).toLp _

/-- Weighted translations are strongly continuous on every actual compact
parameter set. A bounded localized multiplier supplies the proof even when
the global confinement weight is unbounded. -/
theorem planarWeightedTranslateL2_continuousOn_compact
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ)
    (A : Set ℂ) (hA : IsCompact A) :
    ContinuousOn (planarWeightedTranslateL2 n V hV ψ hψ hc) A := by
  let S := A + tsupport ψ
  have hS : IsCompact S := hA.add hc
  have hw : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn hw.continuousOn
  let b : ℂ → ℂ := S.indicator (planarPotentialHalfWeight n V)
  have hb : AEStronglyMeasurable b volume := hw.aestronglyMeasurable.indicator hS.measurableSet
  have hbn (x : ℂ) : ‖b x‖ ≤ max C 0 := by
    by_cases hx : x ∈ S
    · simp only [b, Set.indicator_of_mem hx]
      exact (hC x hx).trans (le_max_left _ _)
    · simp only [b, Set.indicator_of_notMem hx, norm_zero]
      exact le_max_right _ _
  let T := boundedComplexL2Multiplier b hb (max C 0) hbn
  have hm : MemLp ψ 2 volume := hψ.memLp_of_hasCompactSupport hc
  let τ : ℂ → PlanarLebesgueL2 := fun a => DomAddAct.mk (-a) +ᵥ hm.toLp ψ
  have hτ : Continuous τ := (DomAddAct.continuous_mk.comp continuous_neg).vadd continuous_const
  have he (a : ℂ) (ha : a ∈ A) : planarWeightedTranslateL2 n V hV ψ hψ hc a = T (τ a) := by
    apply Lp.ext
    have ht := DomAddAct.vadd_Lp_ae_eq (DomAddAct.mk (-a)) (hm.toLp ψ)
    have htp := (eventually_add_right_iff (volume : Measure ℂ) (-a)).mpr hm.coeFn_toLp
    filter_upwards [(planarWeightedTranslate_memLp n V hV ψ hψ hc a).coeFn_toLp,
      boundedComplexL2Multiplier_coeFn b hb (max C 0) hbn (τ a), ht, htp] with x hx hTx htr hψx
    change (planarWeightedTranslate_memLp n V hV ψ hψ hc a).toLp _ x =
      boundedComplexL2Multiplier b hb (max C 0) hbn (τ a) x
    rw [hx, hTx]
    have htrx : (τ a) x = ψ (x - a) := by
      have htr' : (τ a) x = (hm.toLp ψ) (x - a) := by
        simpa only [τ, Equiv.symm_apply_apply, vadd_eq_add, sub_eq_add_neg, add_comm] using htr
      exact htr'.trans (by simpa only [sub_eq_add_neg] using hψx)
    rw [htrx]
    change ψ (x - a) * planarPotentialHalfWeight n V x = b x * ψ (x - a)
    by_cases hz : ψ (x - a) = 0
    · simp [hz]
    · have hs : x ∈ S := Set.mem_add.mpr ⟨a, ha, x - a,
        subset_closure (by exact hz : x - a ∈ Function.support ψ), by abel⟩
      simp only [b, Set.indicator_of_mem hs]
      exact mul_comm _ _
  exact (T.continuous.comp hτ).continuousOn.congr (fun a ha => he a ha)
/-- Weighted compact translations are genuinely strongly continuous for
all translation parameters, proved by compact localization around each. -/
theorem planarWeightedTranslateL2_continuous
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V)
    (ψ : ℂ → ℂ) (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    Continuous (planarWeightedTranslateL2 n V hV ψ hψ hc) := by
  apply continuous_iff_continuousAt.mpr
  intro a
  exact (planarWeightedTranslateL2_continuousOn_compact n V hV ψ hψ hc
    (Metric.closedBall a 1) (isCompact_closedBall a 1)).continuousAt
      (Metric.closedBall_mem_nhds a zero_lt_one)

end
end GinibrePoincare
