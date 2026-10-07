module

public import GinibrePoincare.Analysis.GinibreStochasticGaussianPiCrossMoments

@[expose] public section

/-! Distinct actual Brownian coordinates have zero cross bracket in the whole family filtration. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownianFamilyFiltration_cross_conditional {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i j : ι) (hij : i ≠ j)
    (s t : ℝ≥0) (hst : s ≤ t) :
    P[(fun ω => B i t ω*B j t ω) | ginibreBrownianFamilyFiltration B P hB s] =ᵐ[P]
      (fun ω => B i s ω*B j s ω) := by
  let := (hB i).isGaussianProcess.isProbabilityMeasure
  let Past := fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω
  let Z := fun ω k => B k t ω-B k s ω
  let ν := Measure.pi (fun _ : ι => gaussianReal 0 (t-s))
  have hPast : Measurable Past := by
    apply measurable_pi_lambda
    intro p
    exact aemeasurable_iff_measurable.mp ((hB p.1).aemeasurable p.2)
  have hZ : HasLaw Z ν P := by
    simpa only [Z, add_tsub_cancel_of_le hst] using ginibreBrownian_family_increment_hasLaw B P hB hind s (t-s)
  have hInd : IndepFun Z Past P := by
    simpa only [Z, Past, add_tsub_cancel_of_le hst] using
      ginibreBrownian_family_increment_independent_past B P hB hind s (t-s)
  let G : ((ι × Set.Iic s) → ℝ) × (ι → ℝ) → ℝ := fun p =>
    (p.1 (i, ⟨s, by change s ≤ s; exact le_rfl⟩)+p.2 i)*
      (p.1 (j, ⟨s, by change s ≤ s; exact le_rfl⟩)+p.2 j)
  have hG : Measurable G := by fun_prop
  have hEq : (fun ω => G (Past ω,Z ω)) =ᵐ[P] (fun ω => B i t ω*B j t ω) :=
    Filter.Eventually.of_forall fun ω => by dsimp [G, Past, Z]; ring
  have hProd : Integrable (fun ω => B i t ω*B j t ω) P :=
    ((hB i).isGaussianProcess.hasGaussianLaw_eval t).memLp_two.integrable_mul
      ((hB j).isGaussianProcess.hasGaussianLaw_eval t).memLp_two
  have hGi := hProd.congr hEq.symm
  have hCondω := ae_of_ae_map hPast.aemeasurable
    (ginibreIndependent_condDistrib_general P Past Z hPast ν hZ hInd)
  have hCE := condExp_prod_ae_eq_integral_condDistrib hPast hZ.aemeasurable hG.stronglyMeasurable hGi
  have h := ((condExp_congr_ae (m := MeasurableSpace.comap Past inferInstance) hEq).symm.trans hCE)
  change P[(fun ω => B i t ω*B j t ω) | MeasurableSpace.comap Past inferInstance] =ᵐ[P] _
  apply h.trans
  filter_upwards [hCondω] with ω hκ
  change (∫ u, (B i s ω+u i)*(B j s ω+u j) ∂condDistrib Z Past P (Past ω)) = _
  rw [hκ]
  exact ginibreGaussianPi_shifted_crossMoment (t-s) i j hij (B i s ω) (B j s ω)

theorem ginibreBrownianFamilyFiltration_cross_martingale {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (i j : ι) (hij : i ≠ j) :
    Martingale (fun t ω => B i t ω*B j t ω) (ginibreBrownianFamilyFiltration B P hB) P := by
  refine ⟨fun s => (ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB i s).mul
    (ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted B P hB j s), ?_⟩
  intro s t hst
  exact ginibreBrownianFamilyFiltration_cross_conditional B P hB hind i j hij s t hst

end
end GinibrePoincare
