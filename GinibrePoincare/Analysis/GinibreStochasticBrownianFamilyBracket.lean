module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyMartingale
public import GinibrePoincare.Analysis.GinibreStochasticCIRMoments

@[expose] public section

/-! Actual Brownian square brackets in the full family filtration. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownianFamilyFiltration_square_conditional {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i : ι) (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => (B i t ω)^2) | ginibreBrownianFamilyFiltration B P hB s] =ᵐ[P]
      (fun ω => (B i s ω)^2+(t-s : ℝ≥0)) := by
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω
  let Z := fun ω => B i t ω-B i s ω
  let ν := gaussianReal 0 (t-s)
  have hPast : Measurable Past := by
    apply measurable_pi_lambda
    intro p
    exact aemeasurable_iff_measurable.mp ((hB p.1).aemeasurable p.2)
  have hZ : HasLaw Z ν P := ginibreBrownian_increment_hasLaw (B i) P (hB i) s t hst
  have hInd := (ginibreBrownian_family_increment_independent_past B P hB hind s (t-s)).comp
    (measurable_pi_apply i) measurable_id
  have hInd' : IndepFun Z Past P := by
    simpa only [Z, Past, Function.comp_def, id_eq, add_tsub_cancel_of_le hst] using hInd
  let G : ((ι × Set.Iic s) → ℝ) × ℝ → ℝ :=
    fun p => (p.1 (i, ⟨s, by change s ≤ s; exact le_rfl⟩)+p.2)^2
  have hG : Measurable G := by fun_prop
  have hEq : (fun ω => G (Past ω, Z ω)) =ᵐ[P] (fun ω => (B i t ω)^2) :=
    Filter.Eventually.of_forall fun ω => by dsimp [G, Past, Z]; ring
  have hGi : Integrable (fun ω => G (Past ω, Z ω)) P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq.congr hEq.symm
  have hCondω := ae_of_ae_map hPast.aemeasurable (ginibreIndependent_condDistrib P Past Z hPast ν hZ hInd')
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable hGi
  have h := ((condExp_congr_ae (m := MeasurableSpace.comap Past inferInstance) hEq).symm.trans hCE)
  change P[(fun ω => (B i t ω)^2) | MeasurableSpace.comap Past inferInstance] =ᵐ[P] _
  apply h.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ u, (B i s ω+u)^2 ∂condDistrib Z Past P (Past ω)) = _
  rw [hκ]
  change (∫ u, (B i s ω+u)^2 ∂gaussianReal 0 (t-s)) = _
  rw [ginibreGaussian_shifted_secondMoment]
  ring

theorem ginibreBrownianFamilyFiltration_square_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i : ι) :
    Martingale (fun t ω => (B i t ω)^2-(t : ℝ)) (ginibreBrownianFamilyFiltration B P hB) P := by
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  have hAdapt := ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB i
  refine ⟨fun s => (hAdapt s).pow 2 |>.sub stronglyMeasurable_const, ?_⟩
  intro s t hst
  have hSq := ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_sq
  have hSub := condExp_sub hSq (integrable_const (t : ℝ)) (ginibreBrownianFamilyFiltration B P hB s)
  rw [condExp_const (ginibreBrownianFamilyFiltration B P hB |>.le s)] at hSub
  simp only [Pi.sub_def] at hSub
  have hCE := ginibreBrownianFamilyFiltration_square_conditional B P hB hind i s t hst
  filter_upwards [hSub, hCE] with ω hω he
  rw [NNReal.coe_sub hst] at he
  linarith

end
end GinibrePoincare
