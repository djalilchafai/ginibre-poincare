module

public import GinibrePoincare.Analysis.GeneralRadialProjectionModes

@[expose] public section

open MeasureTheory Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem planarBergman_negative_phase_eq_zero
    (n k : ℕ) (hk : 0 < k) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a * z) = V z)
    (u : PlanarLebesgueL2) (hu : u ∈ planarBergmanKernel n V hV)
    (hp : ∀ (a : ℂ) (ha : ‖a‖ = 1), planarLebesguePhase a ha u = a ^ (-(k : ℤ)) • u) :
    u = 0 := by
  obtain ⟨F, hF, hm, he⟩ :=
    (mem_planarWeakDbarKernel_iff_holomorphic_representative n V hV u).mp hu
  have hwc : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  have hcov (a : ℂ) (ha : ‖a‖ = 1) : ∀ z, F (a * z) = a ^ (-(k : ℤ)) * F z := by
    let mp := measurePreserving_complex_mul_of_norm_one a ha
    have hup := hp a ha
    rw [← he] at hup
    have hc := Lp.coeFn_compMeasurePreserving (hm.toLp _) mp
    have haF := mp.quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp
    have hae : (fun z => F (a * z) * planarPotentialHalfWeight n V (a * z)) =ᵐ[volume]
        (fun z => a ^ (-(k : ℤ)) * (F z * planarPotentialHalfWeight n V z)) := by
      filter_upwards [hc, haF, hm.coeFn_toLp, Lp.coeFn_smul (a ^ (-(k : ℤ))) (hm.toLp _)] with z hz hzF hz0 hzs
      have hv := congrArg (fun w : PlanarLebesgueL2 => w z) hup
      change (Lp.compMeasurePreserving (fun z : ℂ => a * z) mp (hm.toLp _)) z = _ at hv
      rw [hz, hzF, hzs] at hv
      change F (a * z) * planarPotentialHalfWeight n V (a * z) = a ^ (-(k : ℤ)) * (hm.toLp _) z at hv
      rw [hz0] at hv
      exact hv
    have heq := ((hF.continuous.comp (continuous_const.mul continuous_id)).mul
      (hwc.comp (continuous_const.mul continuous_id))).ae_eq_iff_eq volume
      (continuous_const.mul (hF.continuous.mul hwc)) |>.mp hae
    intro z
    have hz := congrFun heq z
    change F (a * z) * planarPotentialHalfWeight n V (a * z) = a ^ (-(k : ℤ)) * (F z * planarPotentialHalfWeight n V z) at hz
    have hw : planarPotentialHalfWeight n V (a * z) = planarPotentialHalfWeight n V z := by
      simp only [planarPotentialHalfWeight, hr a ha z]
    rw [hw, ← mul_assoc] at hz
    exact mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) hz
  have hz : ∀ z, F z = 0 := entire_negative_phase_eq_zero F hF k hk
    (fun a ha => by simpa using hcov a ha 1)
  have hfzero : (fun z => F z * planarPotentialHalfWeight n V z) = (0 : ℂ → ℂ) := by
    funext z
    simp [hz]
  have hezero : hm.toLp _ = 0 := by
    apply Lp.ext
    filter_upwards [hm.coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume : Measure ℂ)] with z he hz0
    rw [he, hz, zero_mul, hz0]
    rfl
  exact he.symm.trans hezero

end
end GinibrePoincare
