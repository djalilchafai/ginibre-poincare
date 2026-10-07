module

public import GinibrePoincare.Analysis.GeneralPotentialVandermondeGauge

@[expose] public section

open MeasureTheory
open scoped ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialCentered_memLp (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    MemLp (fun z => ((f z - ∫ w, f w ∂potentialMeasure n V : ℝ) : ℂ)) 2
      (potentialMeasure n V) := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact (hf.sub (memLp_const _)).ofReal

def potentialCenteredL2 (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    Lp ℂ 2 (potentialMeasure n V) :=
  (potentialCentered_memLp n hn hV hfin f hf).toLp _

theorem potentialCenteredL2_coeFn (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    (potentialCenteredL2 n hn hV hfin f hf : Configuration n → ℂ) =ᵐ[potentialMeasure n V]
      fun z => ((f z - ∫ w, f w ∂potentialMeasure n V : ℝ) : ℂ) :=
  (potentialCentered_memLp n hn hV hfin f hf).coeFn_toLp

theorem potentialCenteredL2_norm_sq (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    ‖potentialCenteredL2 n hn hV hfin f hf‖ ^ 2 = potentialVariance n V f := by
  have he : inner ℂ (potentialCenteredL2 n hn hV hfin f hf)
      (potentialCenteredL2 n hn hV hfin f hf) =
      ∫ z, inner ℂ ((potentialCenteredL2 n hn hV hfin f hf) z)
        ((potentialCenteredL2 n hn hV hfin f hf) z) ∂potentialMeasure n V :=
    L2.inner_def _ _
  rw [inner_self_eq_norm_sq_to_K] at he
  have hc := potentialCenteredL2_coeFn n hn hV hfin f hf
  rw [integral_congr_ae (by
    filter_upwards [hc] with z hz
    rw [hz])] at he
  have hi (r : ℝ) : inner ℂ (r : ℂ) (r : ℂ) = (r ^ 2 : ℝ) := by
    simp only [RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, pow_two]
  simp_rw [hi] at he
  rw [integral_complex_ofReal] at he
  apply Complex.ofReal_injective
  convert he using 1 <;> simp [Complex.ofReal_pow, potentialVariance]

theorem potentialVandermondeCentered_norm_sq (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    ‖potentialVandermondeL2 n hn hV hfin (potentialCenteredL2 n hn hV hfin f hf)‖ ^ 2 =
      potentialVariance n V f := by
  rw [(potentialVandermondeL2 n hn hV hfin).norm_map]
  exact potentialCenteredL2_norm_sq n hn hV hfin f hf

theorem potentialSmoothCompact_memLp (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    MemLp f 2 (potentialMeasure n V) := by
  letI := potentialMeasure_isProbabilityMeasure n hn hV hfin
  exact hf.memLp_of_hasCompactSupport hc

end
end GinibrePoincare
