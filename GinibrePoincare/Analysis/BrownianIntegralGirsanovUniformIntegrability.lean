module

public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

open MeasureTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem nonnegativeDensities_uniformIntegrable_of_secondMoment_bound
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (f : ℕ → Ω → ℝ) (hm : ∀ n, Measurable (f n)) (hp : ∀ n ω, 0≤f n ω)
    (R : ℝ) (hR : 0≤R)
    (h2 : ∀ n, (∫⁻ ω, ENNReal.ofReal (f n ω)^2 ∂P) ≤ ENNReal.ofReal R) :
    UniformIntegrable f 1 P := by
  apply uniformIntegrable_of (by norm_num) (by norm_num) (fun n => (hm n).aestronglyMeasurable)
  intro ε' hε'
  by_cases htop : ε' = ∞
  · exact ⟨0, fun _ => htop ▸ le_top⟩
  let ε : ℝ := ε'.toReal
  have hε : 0 < ε := ENNReal.toReal_pos hε'.ne' htop
  let K : ℝ≥0 := ⟨(R+1)/ε,by positivity⟩
  have hK : (0 : ℝ)<K := by change 0<(R+1)/ε; positivity
  refine ⟨K,fun n => ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm
    ((hm n).aestronglyMeasurable.indicator
      (measurableSet_le measurable_const (hm n).nnnorm))]
  have hpoint (ω : Ω) : ‖({ω | K≤‖f n ω‖₊}.indicator (f n)) ω‖ₑ ≤
      ENNReal.ofReal (1/(K : ℝ))*ENNReal.ofReal (f n ω)^2 := by
    by_cases hk : ω∈{ω | K≤‖f n ω‖₊}
    · rw [Set.indicator_of_mem hk]
      rw [← ENNReal.ofReal_pow (hp n ω) 2,← ENNReal.ofReal_mul (by positivity)]
      rw [Real.enorm_eq_ofReal (hp n ω)]
      apply ENNReal.ofReal_le_ofReal
      have hkle : (K : ℝ)≤f n ω := by
        have hh : (K : ℝ)≤‖f n ω‖ := by exact_mod_cast hk
        simpa only [Real.norm_eq_abs,abs_of_nonneg (hp n ω)] using hh
      rw [one_div_mul_eq_div]
      exact (le_div_iff₀ hK).mpr (by nlinarith)
    · rw [Set.indicator_of_notMem hk,enorm_zero]
      exact bot_le
  calc
    _ ≤ ∫⁻ ω, ENNReal.ofReal (1/(K : ℝ))*ENNReal.ofReal (f n ω)^2 ∂P := lintegral_mono hpoint
    _ = ENNReal.ofReal (1/(K : ℝ))*(∫⁻ ω, ENNReal.ofReal (f n ω)^2 ∂P) := by
      have hmeas : Measurable (fun ω => ENNReal.ofReal (f n ω)^2) := by fun_prop
      rw [lintegral_const_mul _ hmeas]
    _ ≤ ENNReal.ofReal (1/(K : ℝ))*ENNReal.ofReal R := mul_le_mul' le_rfl (h2 n)
    _ ≤ ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [one_div_mul_eq_div]
      apply (div_le_iff₀ hK).mpr
      change R ≤ ε*((R+1)/ε)
      rw [mul_div_cancel₀ _ hε.ne']
      linarith
    _ = ε' := ENNReal.ofReal_toReal htop

end
end GinibrePoincare
