module

public import GinibrePoincare.Analysis.GinibreHamiltonianCompletedProductBrownian
public import GinibrePoincare.Analysis.GinibreHamiltonianActualStationaryOUReversal

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1800000
local instance ginibreCompletedStationaryReference_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreCompletedStationaryReference_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Actual stationary killed OU action reversal on the explicit completed
Gaussian-coordinate/original-Brownian product. All initial independence and
Brownian transport properties are derived internally. -/
theorem ginibreHamiltonian_completed_product_killed_action_reverse {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (R : ℝ) :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    let ν := γ.prod P
    let Q := ν.completion
    let A := fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
      ginibreHamiltonianOUJointHorizonPath n α T
        (ginibreHamiltonianOUCoordinateAssembly n x.1,
          ginibreBrownianFullContinuousNoise n (fun i t y => B i t y.2) α x)
    ((Q.map A).withDensity (fun x => ENNReal.ofReal
      (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      (Q.map A).withDensity (fun x => ENNReal.ofReal
        (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x)) := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let ν := γ.prod P
  let Q := ν.completion
  let Ωc := NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν
  haveI : IsProbabilityMeasure Q := ginibre_completion_isProbabilityMeasure ν
  let Bc : (Fin n × Fin 2) → ℝ≥0 → Ωc → ℝ := fun i t x => B i t x.2
  let Z : (Fin n × Fin 2) → Ωc → ℝ := fun i x => x.1 i
  have hBc : ∀ i, IsBrownianReal (Bc i) Q := ginibreBrownian_completed_initial_noise_product γ P B hB
  have hZ (i : Fin n × Fin 2) : HasLaw (Z i) (gaussianReal 0 (1/2)) Q :=
    (measurePreserving_eval (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2)) i).hasLaw.comp
      (ginibreCompletedProduct_fst_preserving γ P).hasLaw
  have hiZ : iIndepFun Z Q := ginibre_iIndepFun_precompose_measurePreserving Q γ _
    (ginibreCompletedProduct_fst_preserving γ P) (fun i x => x i)
      (fun i => measurable_pi_apply i)
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id))
  have hiBc : iIndepFun (fun i x t => Bc i t x) Q :=
    ginibreBrownian_completed_product_independent_coordinates γ P B hB hiB
  have hm : Measurable (fun ω i t => B i t ω) :=
    Measurable.of_eval (fun i => Measurable.of_eval
      (fun t => aemeasurable_iff_measurable.mp ((hB i).aemeasurable t)))
  have hind : IndepFun (fun x i => Z i x) (fun x i t => Bc i t x) Q :=
    (ginibreCompletedProduct_initial_noise_independent γ P).comp measurable_id hm
  exact ginibreHamiltonian_actual_stationary_killed_action_reverse hn α hα Q Bc hBc Z hZ hiZ hiBc hind T R

#print axioms ginibreHamiltonian_completed_product_killed_action_reverse
end
end GinibrePoincare
