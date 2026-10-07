module

public import GinibrePoincare.Analysis.GinibreStochasticCIRMoments

@[expose] public section

/-! # Actual quadratic conditional moments, with Gaussian integrability proved -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreBrownianOU_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) (x : ℝ) :
    MemLp (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x t) 2 P := by
  have hLaw := ginibreBrownianOU_hasLaw B P hB rate t x
  have h : MemLp id 2 (ginibreOUTransition rate t x) := by
    change MemLp id 2 (gaussianReal _ _)
    exact IsGaussian.memLp_two_id
  rw [← hLaw.map_eq] at h
  simpa only [Function.comp_def, id_eq] using
    (memLp_map_measure_iff (by fun_prop) hLaw.aemeasurable).mp h

 theorem ginibreGaussian_product_radius_integral (mr mi : ℝ) (v : ℝ≥0) :
    (∫ p : ℝ × ℝ, p.1^2+p.2^2 ∂(gaussianReal mr v).prod (gaussianReal mi v)) =
      mr^2+mi^2+2*(v : ℝ) := by
  have hr : Integrable (fun x : ℝ => x^2) (gaussianReal mr v) :=
    (IsGaussian.memLp_two_id (μ := gaussianReal mr v)).integrable_sq
  have hi : Integrable (fun x : ℝ => x^2) (gaussianReal mi v) :=
    (IsGaussian.memLp_two_id (μ := gaussianReal mi v)).integrable_sq
  rw [integral_add (hr.comp_fst _) (hi.comp_snd _)]
  have hf : HasLaw Prod.fst (gaussianReal mr v) ((gaussianReal mr v).prod (gaussianReal mi v)) :=
    measurePreserving_fst.hasLaw
  have hs : HasLaw Prod.snd (gaussianReal mi v) ((gaussianReal mr v).prod (gaussianReal mi v)) :=
    measurePreserving_snd.hasLaw
  have hrf := hf.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)
  have hif := hs.integral_comp (f := fun x : ℝ => x^2) (by fun_prop)
  change (∫ p : ℝ × ℝ, p.1^2 ∂(gaussianReal mr v).prod (gaussianReal mi v)) +
    (∫ p : ℝ × ℝ, p.2^2 ∂(gaussianReal mr v).prod (gaussianReal mi v)) = _
  rw [show (∫ p : ℝ × ℝ, p.1^2 ∂(gaussianReal mr v).prod (gaussianReal mi v)) =
      (v : ℝ)+mr^2 from hrf.trans (ginibreGaussian_secondMoment mr v),
    show (∫ p : ℝ × ℝ, p.2^2 ∂(gaussianReal mr v).prod (gaussianReal mi v)) =
      (v : ℝ)+mi^2 from hif.trans (ginibreGaussian_secondMoment mi v)]
  ring

 theorem ginibreBrownianOU_planar_quadratic_conditional {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω u => Br u ω) (fun ω u => Bi u ω) P)
    (rate s t : ℝ≥0) (xr xi : ℝ) :
    P[(fun ω => (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr (s+t) ω)^2+
        (ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi (s+t) ω)^2) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => (ginibreOUDecay rate t)^2*
        ((ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr s ω)^2+
          (ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi s ω)^2)+
            2*(ginibreOUVariance rate t : ℝ)) := by
  have hint := (ginibreBrownianOU_memLp_two Br P hBr rate (s+t) xr).integrable_sq.add
    (ginibreBrownianOU_memLp_two Bi P hBi rate (s+t) xi).integrable_sq
  have h := ginibreBrownianOU_planar_whole_past_markov_integrable Br Bi P hBr hBi hind
    rate s t xr xi (fun p : ℝ × ℝ => p.1^2+p.2^2) (by fun_prop) hint
  apply h.trans
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  change (∫ p : ℝ × ℝ, p.1^2+p.2^2 ∂(gaussianReal _ _).prod (gaussianReal _ _)) = _
  rw [ginibreGaussian_product_radius_integral]
  ring

end
end GinibrePoincare
