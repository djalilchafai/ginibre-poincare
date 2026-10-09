module

public import GinibrePoincare.Analysis.GinibreHamiltonianTransitionKernel
public import GinibrePoincare.Analysis.BrownianOrthogonalGlobalFactorization

@[expose] public section

/-! Exact product of the actual center and relative transition laws. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal ProbabilityTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem ginibreBrownianTransitionKernel_center_relative_product
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (t : ℝ≥0) :
    (ginibreBrownianTransitionKernel hn α B P t).map
      (fun z : Configuration n => (coordinateSum z, recenteredConfiguration n z)) =
      ((ginibreBrownianTransitionKernel hn α B P t).map coordinateSum) ×ₖ
        ((ginibreBrownianTransitionKernel hn α B P t).map (recenteredConfiguration n)) := by
  let K := ginibreBrownianTransitionKernel hn α B P t
  have hK : IsMarkovKernel K := ginibreBrownianTransitionKernel_isMarkov hn α B P hB t
  letI := hK
  have hS : Measurable (coordinateSum : Configuration n → ℂ) :=
    by
      have he : (fun z => coordinateSumCLM n z)=(coordinateSum : Configuration n → ℂ) := funext (coordinateSumCLM_apply n)
      rw [← he]
      exact (coordinateSumCLM n).continuous.measurable
  have hW : Measurable (recenteredConfiguration n : Configuration n → Configuration n) :=
    by
      have he : (fun z => recenteredCLM n z)=recenteredConfiguration n := funext (recenteredCLM_apply n)
      rw [← he]
      exact (recenteredCLM n).continuous.measurable
  letI : IsMarkovKernel (K.map coordinateSum) := Kernel.IsMarkovKernel.map K hS
  letI : IsMarkovKernel (K.map (recenteredConfiguration n)) := Kernel.IsMarkovKernel.map K hW
  ext1 z
  rw [Kernel.map_apply _ (hS.prodMk hW), Kernel.prod_apply,
    Kernel.map_apply _ hS, Kernel.map_apply _ hW]
  change (K z).map (fun x => (coordinateSum x, recenteredConfiguration n x)) =
    ((K z).map coordinateSum).prod ((K z).map (recenteredConfiguration n))
  have hX : Measurable (ginibreBrownianMaximalProcess n α z.val B t) :=
    (ginibreDrivenMaximalValue_measurable hn α z.val t).comp
      (ginibreBrownianFullContinuousNoise_measurable n B P hB α)
  rw [show K z=P.map (ginibreBrownianMaximalProcess n α z.val B t) from
    ginibreBrownianTransitionKernel_apply_eq_process_law hn α B P hB t z,
    Measure.map_map (hS.prodMk hW) hX, Measure.map_map hS hX, Measure.map_map hW hX]
  have hi := (ginibreBrownian_center_relative_processes_independent hn α z.val z.property B P hB hind).comp
    (measurable_pi_apply t) (measurable_pi_apply t)
  exact hi.map_prod_eq_prod_map_map (hS.comp hX).aemeasurable (hW.comp hX).aemeasurable

end
end GinibrePoincare
