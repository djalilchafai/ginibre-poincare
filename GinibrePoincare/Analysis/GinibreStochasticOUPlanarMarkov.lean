module

public import GinibrePoincare.Analysis.GinibreStochasticOUPlanarInnovation
public import GinibrePoincare.Analysis.GinibreStochasticOUWholePastMarkov

@[expose] public section

/-! # Full joint-past Markov formula for the actual planar OU convolution -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 @[instance_reducible] def ginibrePlanarBrownianPastMeasurableSpace {Ω : Type*}
    (Br Bi : ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace ((Set.Iic s → ℝ) × (Set.Iic s → ℝ))).comap
    (fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω)))

 theorem ginibreBrownianOU_planar_whole_past_markov {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω => fun u => Br u ω) (fun ω => fun u => Bi u ω) P)
    (rate s t : ℝ≥0) (xr xi : ℝ) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (C : ℝ) (hbound : ∀ y, ‖f y‖ ≤ C) :
    P[(fun ω => f (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr (s+t) ω,
        ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi (s+t) ω)) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ y, f y ∂((ginibreOUTransition rate t
        (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr s ω)).prod
          (ginibreOUTransition rate t (ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi s ω)))) := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))
  let U := fun ω => (ginibreBrownianOUInnovation Br rate s t ω,
    ginibreBrownianOUInnovation Bi rate s t ω)
  let ν := (gaussianReal 0 (ginibreOUVariance rate t)).prod
    (gaussianReal 0 (ginibreOUVariance rate t))
  let Ψr := ginibreOUPastFunctional rate s xr
  let Ψi := ginibreOUPastFunctional rate s xi
  let G : ((Set.Iic s → ℝ) × (Set.Iic s → ℝ)) × (ℝ × ℝ) → ℝ :=
    fun p => f (ginibreOUDecay rate t * Ψr p.1.1 + p.2.1,
      ginibreOUDecay rate t * Ψi p.1.2 + p.2.2)
  have hPast : Measurable Past := by
    apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro v
    · exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
    · exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  have hU : HasLaw U ν P := ginibreBrownianOU_planar_innovations_hasLaw Br Bi P hBr hBi hind rate s t
  have hInd : IndepFun U Past P :=
    ginibreBrownianOU_planar_innovations_independent_past Br Bi P hBr hBi hind rate s t
  have hCond := ginibreIndependent_condDistrib_general P Past U hPast ν hU hInd
  have hCondω := ae_of_ae_map hPast.aemeasurable hCond
  have hG : Measurable G := by
    apply hf.comp
    apply Measurable.prodMk
    · exact (measurable_const.mul ((ginibreOUPastFunctional_measurable rate s xr).comp
        (measurable_fst.comp measurable_fst))).add (measurable_fst.comp measurable_snd)
    · exact (measurable_const.mul ((ginibreOUPastFunctional_measurable rate s xi).comp
        (measurable_snd.comp measurable_fst))).add (measurable_snd.comp measurable_snd)
  have hGint : Integrable (fun ω => G (Past ω, U ω)) P := by
    apply (integrable_const C).mono'
    · exact (hG.comp_aemeasurable (hPast.aemeasurable.prodMk hU.aemeasurable)).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun ω => hbound _
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hU.aemeasurable hG.stronglyMeasurable hGint
  have hΨr := ginibreOUPastFunctional_ae_eq Br P hBr rate s xr
  have hΨi := ginibreOUPastFunctional_ae_eq Bi P hBi rate s xi
  have hsr := ginibreBrownianOU_step_ae Br P hBr rate s t xr
  have hsi := ginibreBrownianOU_step_ae Bi P hBi rate s t xi
  have he : (fun ω => f (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr (s+t) ω,
      ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi (s+t) ω)) =ᵐ[P]
      (fun ω => G (Past ω, U ω)) := by
    filter_upwards [hΨr, hΨi, hsr, hsi] with ω hr hi hsr hsi
    dsimp [G, Ψr, Ψi, Past, U]
    rw [hr, hi, hsr, hsi]
  apply ((condExp_congr_ae (m := ginibrePlanarBrownianPastMeasurableSpace Br Bi s) he).trans hCE).trans
  filter_upwards [hCondω, hΨr, hΨi] with ω hκ hr hi
  change (∫ u, f (ginibreOUDecay rate t * Ψr (Past ω).1 + u.1,
    ginibreOUDecay rate t * Ψi (Past ω).2 + u.2) ∂condDistrib U Past P (Past ω)) = _
  rw [hκ]
  change (∫ u, f (ginibreOUDecay rate t * Ψr (Past ω).1 + u.1,
    ginibreOUDecay rate t * Ψi (Past ω).2 + u.2) ∂ν) = _
  change Ψr (Past ω).1 = _ at hr
  change Ψi (Past ω).2 = _ at hi
  rw [hr, hi]
  have hk (y : ℝ) : ginibreOUTransition rate t y =
      (gaussianReal 0 (ginibreOUVariance rate t)).map (fun u : ℝ => ginibreOUDecay rate t * y + u) := by
    change gaussianReal (ginibreOUDecay rate t * y) (ginibreOUVariance rate t) = _
    rw [gaussianReal_map_const_add, zero_add]
  rw [hk, hk, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) hf.stronglyMeasurable.aestronglyMeasurable]
  rfl
 theorem ginibreBrownianOU_planar_whole_past_markov_integrable {Ω : Type*} [MeasurableSpace Ω]
    (Br Bi : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hBr : IsBrownianReal Br P) (hBi : IsBrownianReal Bi P)
    (hind : IndepFun (fun ω => fun u => Br u ω) (fun ω => fun u => Bi u ω) P)
    (rate s t : ℝ≥0) (xr xi : ℝ) (f : ℝ × ℝ → ℝ) (hf : Measurable f)
    (hActual : Integrable (fun ω => f (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr (s+t) ω,
        ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi (s+t) ω)) P) :
    P[(fun ω => f (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr (s+t) ω,
        ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi (s+t) ω)) |
      ginibrePlanarBrownianPastMeasurableSpace Br Bi s] =ᵐ[P]
      (fun ω => ∫ y, f y ∂((ginibreOUTransition rate t
        (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr s ω)).prod
          (ginibreOUTransition rate t (ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi s ω)))) := by
  let := hBr.isGaussianProcess.isProbabilityMeasure
  let Past := fun ω => ((fun v : Set.Iic s => Br v ω), (fun v : Set.Iic s => Bi v ω))
  let U := fun ω => (ginibreBrownianOUInnovation Br rate s t ω,
    ginibreBrownianOUInnovation Bi rate s t ω)
  let ν := (gaussianReal 0 (ginibreOUVariance rate t)).prod
    (gaussianReal 0 (ginibreOUVariance rate t))
  let Ψr := ginibreOUPastFunctional rate s xr
  let Ψi := ginibreOUPastFunctional rate s xi
  let G : ((Set.Iic s → ℝ) × (Set.Iic s → ℝ)) × (ℝ × ℝ) → ℝ :=
    fun p => f (ginibreOUDecay rate t * Ψr p.1.1 + p.2.1,
      ginibreOUDecay rate t * Ψi p.1.2 + p.2.2)
  have hPast : Measurable Past := by
    apply Measurable.prodMk <;> apply measurable_pi_lambda <;> intro v
    · exact aemeasurable_iff_measurable.mp (hBr.aemeasurable v)
    · exact aemeasurable_iff_measurable.mp (hBi.aemeasurable v)
  have hU : HasLaw U ν P := ginibreBrownianOU_planar_innovations_hasLaw Br Bi P hBr hBi hind rate s t
  have hInd : IndepFun U Past P :=
    ginibreBrownianOU_planar_innovations_independent_past Br Bi P hBr hBi hind rate s t
  have hCond := ginibreIndependent_condDistrib_general P Past U hPast ν hU hInd
  have hCondω := ae_of_ae_map hPast.aemeasurable hCond
  have hG : Measurable G := by
    apply hf.comp
    apply Measurable.prodMk
    · exact (measurable_const.mul ((ginibreOUPastFunctional_measurable rate s xr).comp
        (measurable_fst.comp measurable_fst))).add (measurable_fst.comp measurable_snd)
    · exact (measurable_const.mul ((ginibreOUPastFunctional_measurable rate s xi).comp
        (measurable_snd.comp measurable_fst))).add (measurable_snd.comp measurable_snd)
  have hΨr := ginibreOUPastFunctional_ae_eq Br P hBr rate s xr
  have hΨi := ginibreOUPastFunctional_ae_eq Bi P hBi rate s xi
  have hsr := ginibreBrownianOU_step_ae Br P hBr rate s t xr
  have hsi := ginibreBrownianOU_step_ae Bi P hBi rate s t xi
  have he : (fun ω => f (ginibreBrownianOU Br rate (Real.sqrt (rate : ℝ)) xr (s+t) ω,
      ginibreBrownianOU Bi rate (Real.sqrt (rate : ℝ)) xi (s+t) ω)) =ᵐ[P]
      (fun ω => G (Past ω, U ω)) := by
    filter_upwards [hΨr, hΨi, hsr, hsi] with ω hr hi hsr hsi
    dsimp [G, Ψr, Ψi, Past, U]
    rw [hr, hi, hsr, hsi]
  have hGint : Integrable (fun ω => G (Past ω, U ω)) P := hActual.congr he
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hU.aemeasurable hG.stronglyMeasurable hGint
  apply ((condExp_congr_ae (m := ginibrePlanarBrownianPastMeasurableSpace Br Bi s) he).trans hCE).trans
  filter_upwards [hCondω, hΨr, hΨi] with ω hκ hr hi
  change (∫ u, f (ginibreOUDecay rate t * Ψr (Past ω).1 + u.1,
    ginibreOUDecay rate t * Ψi (Past ω).2 + u.2) ∂condDistrib U Past P (Past ω)) = _
  rw [hκ]
  change (∫ u, f (ginibreOUDecay rate t * Ψr (Past ω).1 + u.1,
    ginibreOUDecay rate t * Ψi (Past ω).2 + u.2) ∂ν) = _
  change Ψr (Past ω).1 = _ at hr
  change Ψi (Past ω).2 = _ at hi
  rw [hr, hi]
  have hk (y : ℝ) : ginibreOUTransition rate t y =
      (gaussianReal 0 (ginibreOUVariance rate t)).map (fun u : ℝ => ginibreOUDecay rate t * y + u) := by
    change gaussianReal (ginibreOUDecay rate t * y) (ginibreOUVariance rate t) = _
    rw [gaussianReal_map_const_add, zero_add]
  rw [hk, hk, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    integral_map (by fun_prop) hf.stronglyMeasurable.aestronglyMeasurable]
  rfl

end
end GinibrePoincare
