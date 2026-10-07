module

public import GinibrePoincare.Analysis.GeneralPotentialCompactGap

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialVandermonde_compact_graph_value {d : ℕ}
    (hn : 0 < d+1) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hfin : potentialPartition (d+1) V < ⊤)
    (f : Configuration (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let hmem := potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc
    let g := potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ))
    let hg := potentialVandermondeCoefficient_contDiff V _ (Complex.ofRealCLM.contDiff.comp hf)
    let hgc := potentialVandermondeCoefficient_hasCompactSupport V _
      (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
    (piCompactWeightedDbarGraph (d+1) V hV.continuous g hg hgc).1 =
      potentialVandermondeL2 (d+1) hn hV.continuous hfin (hmem.ofReal.toLp (fun z => (f z : ℂ))) := by
  dsimp only
  apply Lp.ext
  have ha := potentialVandermondeL2_coeFn_public (d+1) hn hV.continuous hfin
    ((potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc).ofReal.toLp
      (fun z => (f z : ℂ)))
  have hm : MemLp (fun z => (f z : ℂ)) 2 (potentialMeasure (d+1) V) :=
    (potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc).ofReal
  have hb := (configurationVolume_absolutelyContinuous_potentialMeasure (d+1) hn hV.continuous hfin).ae_eq
    hm.coeFn_toLp
  have hg : ContDiff ℝ 1 (potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ))) :=
    potentialVandermondeCoefficient_contDiff V _ (Complex.ofRealCLM.contDiff.comp hf)
  have hgc : HasCompactSupport (potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ))) :=
    potentialVandermondeCoefficient_hasCompactSupport V _
    (hc.comp_left (g := Complex.ofReal) Complex.ofReal_zero)
  have hx : MemLp (fun z => potentialVandermondeCoefficient (d+1) V (fun z => (f z : ℂ)) z *
      piPotentialHalfWeight (d+1) (d+1) V z) 2 (volume : Measure (Configuration (d+1))) :=
    (hg.continuous.mul (piPotentialHalfWeight_continuous (d+1) (d+1) V hV.continuous)).memLp_of_hasCompactSupport hgc.mul_right
  filter_upwards [ha, hb, hx.coeFn_toLp] with z hz hb hx
  change (piCompactWeightedDbarGraph (d+1) V hV.continuous _ _ _).1 z = _
  rw [hz, hb]
  change ((hg.continuous.mul (piPotentialHalfWeight_continuous (d+1) (d+1) V hV.continuous)).memLp_of_hasCompactSupport hgc.mul_right).toLp _ z = _
  convert hx.trans (potentialVandermondeCoefficient_weighted (d+1) V _ z) using 1


end
end GinibrePoincare
