module

public import GinibrePoincare.Analysis.GinibreStochasticCIRConditionalMoment

@[expose] public section

/-! # Exact conditional martingale identity of the actual radius

The statement uses conditional expectations in the entire Brownian past.
It does not assume an Itô formula or a quadratic-variation certificate.
-/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreOneParticleBrownianPath_CIR_exponential_conditional {Ω : Type*}
    [MeasurableSpace Ω] (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (α s t : ℝ≥0) (z : Configuration 1) :
    P[(fun ω => Real.exp (4*(α : ℝ)*(s+t : ℝ≥0)) *
        (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z (s+t) ω)-1)) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => Real.exp (4*(α : ℝ)*(s : ℝ))*
        (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω)-1)) := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let R := fun u : ℝ≥0 => fun ω => ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z u ω)
  have hm : ginibrePlanarBrownianPastMeasurableSpace Br Bi s ≤ ‹MeasurableSpace Ω› := by
    apply Measurable.comap_le
    apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro v
    · exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
    · exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  have hR := ginibreOneParticleBrownianPath_radius_integrable Br Bi P hBr hBi α (s+t) z
  have hsub := condExp_sub hR (integrable_const (1 : ℝ)) (ginibrePlanarBrownianPastMeasurableSpace Br Bi s)
  have hmul := condExp_smul (μ := P) (Real.exp (4*(α : ℝ)*(s+t : ℝ≥0)))
    (R (s+t) - fun _ => (1 : ℝ)) (ginibrePlanarBrownianPastMeasurableSpace Br Bi s)
  have hmean := ginibreOneParticleBrownianPath_CIR_conditional_mean Br Bi P hBr hBi hind α s t z
  apply hmul.trans
  filter_upwards [hsub, hmean] with ω hsub hmean
  simp only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply] at *
  change Real.exp (4*(α : ℝ)*(s+t : ℝ≥0)) * (P[R (s+t) - (fun _ => (1 : ℝ)) | ginibrePlanarBrownianPastMeasurableSpace Br Bi s] ω) = _
  rw [hsub, condExp_const hm]
  simp only [NNReal.coe_add]
  rw [hmean]
  have hexp : Real.exp (4*(α : ℝ)*(s+t : ℝ≥0)) * (ginibreOUDecay (2*α) t)^2 =
      Real.exp (4*(α : ℝ)*(s : ℝ)) := by
    unfold ginibreOUDecay
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    congr 1
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
    ring
  calc
    _ = (Real.exp (4*(α : ℝ)*(s+t : ℝ≥0)) * (ginibreOUDecay (2*α) t)^2) *
        (ginibreOneParticleRadius (ginibreOneParticleBrownianPath Br Bi α z s ω)-1) := by simp only [NNReal.coe_add]; ring
    _ = _ := by rw [hexp]

end
end GinibrePoincare
