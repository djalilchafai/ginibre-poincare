module

public import GinibrePoincare.Analysis.StrongConvexQuantileEndpoints
public import GinibrePoincare.Analysis.StrongConvexQuantileCalculus
public import GinibrePoincare.Analysis.StrongConvexRadialCDF
public import Mathlib.Topology.ExtendFrom

@[expose] public section

open Set Filter MeasureTheory
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Actual quantile density profiles extend continuously by zero at both
probability endpoints when the density vanishes at its support endpoints. -/
theorem positive_densityQuantileProfile_continuousOn (F p : ℝ → ℝ)
    (hm : StrictMonoOn F (Ici 0)) (hF0 : F 0 = 0)
    (hr : F '' Ioi 0 = Ioo 0 1) (hp : Continuous p) (hp0 : p 0 = 0)
    (htop : Tendsto p atTop (𝓝 0)) :
    ContinuousOn (densityQuantileProfile F p (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr)
      (Icc 0 1) := by
  let q := increasingCDFQuantileOn F (Ioi 0) (hm.mono Ioi_subset_Ici_self) hr
  let f := p ∘ q
  have hleft : Tendsto f (𝓝[Ioo 0 1] 0) (𝓝 0) := by
    simpa only [hp0] using hp.continuousAt.tendsto.comp
      (increasingCDFQuantileOn_tendsto_zero F hm hF0 hr)
  have hright : Tendsto f (𝓝[Ioo 0 1] 1) (𝓝 0) :=
    htop.comp (increasingCDFQuantileOn_tendsto_atTop F hm hr)
  have hcont : ContinuousOn f (Ioo 0 1) :=
    hp.comp_continuousOn (increasingCDFQuantileOn_continuousOn F (Ioi 0)
      (hm.mono Ioi_subset_Ici_self) hr)
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (Ioo 0 1) := by
    rw [closure_Ioo (by norm_num : (0 : ℝ) ≠ 1)]
  have hc : ContinuousOn (extendFrom (Ioo 0 1) f) (Icc 0 1) := by
    apply continuousOn_extendFrom hclosure
    intro x hx
    rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with (rfl | rfl | hx)
    · exact ⟨0, hleft⟩
    · exact ⟨0, hright⟩
    · exact ⟨f x, hcont x hx⟩
  apply hc.congr
  intro x hx
  rcases eq_endpoints_or_mem_Ioo_of_mem_Icc hx with (rfl | rfl | hx)
  · rw [extendFrom_eq (hclosure (left_mem_Icc.mpr (by norm_num))) hleft]
    simp [densityQuantileProfile]
  · rw [extendFrom_eq (hclosure (right_mem_Icc.mpr (by norm_num))) hright]
    simp [densityQuantileProfile]
  · rw [extendFrom_extends hcont x hx]
    simp [densityQuantileProfile, hx, f, q]

theorem radialConfinementProbabilityDensity_profile_continuousOn
    (n k : ℕ) (hn : 0 < n) (Q : ℝ → ℝ) (hQ : Continuous Q)
    (hi : MeasureTheory.Integrable (radialConfinementDensity n k Q) MeasureTheory.volume)
    (c C : ℝ) (hc : 0 < c) (hbound : ∀ r, 0 < r → c * r ^ 2 + C ≤ Q r) :
    ContinuousOn (densityQuantileProfile
      (densityCDF (radialConfinementProbabilityDensity n k Q))
      (radialConfinementProbabilityDensity n k Q) (Ioi 0)
      ((radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ hi).mono Ioi_subset_Ici_self)
      (radialConfinementProbabilityDensity_CDF_image n k Q hQ hi)) (Icc 0 1) := by
  apply positive_densityQuantileProfile_continuousOn
    (densityCDF (radialConfinementProbabilityDensity n k Q))
    (radialConfinementProbabilityDensity n k Q)
    (radialConfinementProbabilityDensity_CDF_strictMono n k Q hQ hi)
    (radialConfinementProbabilityDensity_CDF_zero n k Q)
    (radialConfinementProbabilityDensity_CDF_image n k Q hQ hi)
    (radialConfinementProbabilityDensity_continuous n k hQ)
  · simp [radialConfinementProbabilityDensity, radialConfinementDensity]
  · change Tendsto (fun r => radialConfinementDensity n k Q r /
      ∫ t, radialConfinementDensity n k Q t) atTop (𝓝 0)
    simpa only [zero_div] using
      (radialConfinementDensity_tendsto_zero n k hn Q c C hc hbound).div_const
        (∫ t, radialConfinementDensity n k Q t)

#print axioms radialConfinementProbabilityDensity_profile_continuousOn
#print axioms positive_densityQuantileProfile_continuousOn
end
end GinibrePoincare
