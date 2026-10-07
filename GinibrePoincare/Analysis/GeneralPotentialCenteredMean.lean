module

public import GinibrePoincare.Analysis.GeneralPotentialProjectionGeometry

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialCenteredL2_integral_zero (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    (∫ z, potentialCenteredL2 n hn hV hfin f hf z ∂potentialMeasure n V) = 0 := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  rw [integral_congr_ae (potentialCenteredL2_coeFn n hn hV hfin f hf),
    integral_complex_ofReal]
  have hfi : Integrable f (potentialMeasure n V) := hf.integrable (by norm_num)
  rw [integral_sub hfi (integrable_const _), integral_const]
  simp

def potentialConstantL2 (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    Lp ℂ 2 (potentialMeasure n V) := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact (memLp_const c).toLp (fun _ => c)

theorem potentialConstantL2_coeFn (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤) (c : ℂ) :
    (potentialConstantL2 n hn hV hfin c : Configuration n → ℂ) =ᵐ[potentialMeasure n V]
      fun _ => c := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact (memLp_const c).coeFn_toLp

theorem potentialCenteredL2_orthogonal_constant (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) (c : ℂ) :
    inner ℂ (potentialConstantL2 n hn hV hfin c) (potentialCenteredL2 n hn hV hfin f hf) = 0 := by
  rw [L2.inner_def]
  rw [integral_congr_ae (by
    filter_upwards [potentialConstantL2_coeFn n hn hV hfin c] with z hz
    rw [hz])]
  simp only [RCLike.inner_apply]
  rw [integral_mul_const, potentialCenteredL2_integral_zero n hn hV hfin f hf, zero_mul]

end
end GinibrePoincare
