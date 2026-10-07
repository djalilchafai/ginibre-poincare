module

public import GinibrePoincare.Analysis.GeneralPotentialCenteredMean

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialCenteredL2_eq_sub_constant (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    potentialCenteredL2 n hn hV hfin f hf =
      hf.ofReal.toLp (fun z => (f z : ℂ)) -
        potentialConstantL2 n hn hV hfin ((∫ z, f z ∂potentialMeasure n V : ℝ) : ℂ) := by
  have hm : MemLp (fun z => (f z : ℂ)) 2 (potentialMeasure n V) := hf.ofReal
  apply Lp.ext
  filter_upwards [potentialCenteredL2_coeFn n hn hV hfin f hf,
    hm.coeFn_toLp, potentialConstantL2_coeFn n hn hV hfin ((∫ z, f z ∂potentialMeasure n V : ℝ) : ℂ),
    Lp.coeFn_sub (hf.ofReal.toLp (fun z => (f z : ℂ)))
      (potentialConstantL2 n hn hV hfin ((∫ z, f z ∂potentialMeasure n V : ℝ) : ℂ))] with z hc hf hk hs
  rw [hc, hs]
  simp only [Pi.sub_apply]
  rw [hf, hk, Complex.ofReal_sub]

end
end GinibrePoincare
