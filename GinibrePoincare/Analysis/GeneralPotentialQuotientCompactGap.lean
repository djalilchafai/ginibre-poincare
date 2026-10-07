module

public import GinibrePoincare.Analysis.GeneralPotentialCompactLift
public import GinibrePoincare.Analysis.GeneralPotentialQuotientProjection

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual source-space quotient-projection residual bound, with the exact
subharmonic constant and the genuine compact observable lift. -/
theorem potentialHolomorphicQuotientProjection_compact_gap {d : ℕ}
    (hn : 0 < d+1) (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hsub : IsRhoSubharmonicPotential ρ V) (hfin : potentialPartition (d+1) V < ⊤)
    (f : Configuration (d+1) → ℝ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    let hmem := potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc
    let u := hmem.ofReal.toLp (fun z => (f z : ℂ))
    ‖u - potentialHolomorphicQuotientProjection hn hV hfin u‖ ^ 2 ≤
      (1 / (2 * ((d+1 : ℕ) : ℝ) * ρ)) * potentialGradientEnergy (d+1) V f := by
  dsimp only
  rw [potentialHolomorphicQuotientProjection_residual_norm]
  have hg := potentialVandermonde_compact_projection_gap ρ hρ hV hsub hfin f hf hc
  have he := potentialVandermonde_compact_graph_value hn hV hfin f hf hc
  dsimp only at hg he
  change _ = potentialPiVandermondeL2Equiv (d+1) hn hV.continuous hfin
    ((potentialSmoothCompact_memLp (d+1) hn hV.continuous hfin f hf.continuous hc).ofReal.toLp
      (fun z => (f z : ℂ))) at he
  rw [he] at hg
  exact hg

#print axioms potentialHolomorphicQuotientProjection_compact_gap
end
end GinibrePoincare
