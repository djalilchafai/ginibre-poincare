module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUCoordinateAssembly
public import GinibrePoincare.Analysis.GinibreHamiltonianScalarOUPairFunction
public import GinibrePoincare.Analysis.GinibreHamiltonianKilledOUPathMeasure

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance ginibreActualStationaryOU_scalarMeasurable (T : ℝ≥0) : MeasurableSpace C(Icc (0 : ℝ≥0) T,ℝ) := borel _
local instance ginibreActualStationaryOU_scalarBorel (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ≥0) T,ℝ) := ⟨rfl⟩
local instance ginibreActualStationaryOU_configMeasurable (n : ℕ) (T : ℝ≥0) : MeasurableSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := borel _
local instance ginibreActualStationaryOU_configBorel (n : ℕ) (T : ℝ≥0) : BorelSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := ⟨rfl⟩

/-- Time reversal for the actual OU process driven by the original independent
Brownian family and independently sampled Gaussian coordinates. -/
theorem ginibreHamiltonian_actual_stationary_OU_horizon_reverse {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (Z : (Fin n × Fin 2) → Ω → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (1/2)) P)
    (hiZ : iIndepFun Z P) (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (hind : IndepFun (fun ω i => Z i ω) (fun ω i t => B i t ω) P) (T : ℝ≥0) :
    (P.map (fun ω => ginibreHamiltonianOUJointHorizonPath n α T
      (ginibreHamiltonianOUCoordinateAssembly n (fun i => Z i ω),ginibreBrownianFullContinuousNoise n B α ω))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    P.map (fun ω => ginibreHamiltonianOUJointHorizonPath n α T
      (ginibreHamiltonianOUCoordinateAssembly n (fun i => Z i ω),ginibreBrownianFullContinuousNoise n B α ω)) := by
  let rate := (2*α/(n : ℝ)).toNNReal
  let X (i : Fin n × Fin 2) := ginibreBrownianOUHorizonPath (B i) (Z i) rate T
  have hmZ (i : Fin n × Fin 2) : Measurable (Z i) := aemeasurable_iff_measurable.mp (hZ i).aemeasurable
  have hp (i : Fin n × Fin 2) : IndepFun (Z i) (fun ω t => B i t ω) P :=
    hind.comp (measurable_pi_apply i) (measurable_pi_apply i)
  have hm (i : Fin n × Fin 2) : Measurable (X i) :=
    ginibreBrownianOUHorizonPath_measurable (B i) P (hB i) (Z i) (hZ i).hasGaussianLaw (hp i) rate T
  have hi := ginibreScalarOUHorizon_independent_coordinates P B hB Z hmZ hiZ hiB hind rate T
  let μ (i : Fin n × Fin 2) := P.map (X i)
  let R : C(Icc (0 : ℝ≥0) T,ℝ) → C(Icc (0 : ℝ≥0) T,ℝ) :=
    fun x => x.comp (ginibreOUHorizonReverseTime T)
  have hR : Measurable R := (ContinuousMap.continuous_precomp (ginibreOUHorizonReverseTime T)).measurable
  have hμ (i : Fin n × Fin 2) : (μ i).map R = μ i := by
    rw [Measure.map_map hR (hm i)]
    exact (ginibreBrownianOU_stationary_continuous_horizon_law_reversal
      (B i) P (hB i) (Z i) (hZ i) (hp i) rate T).symm
  haveI (i : Fin n × Fin 2) : IsProbabilityMeasure (μ i) := (by infer_instance)
  haveI (i : Fin n × Fin 2) : IsProbabilityMeasure ((μ i).map R) := (by infer_instance)
  have hpi : (Measure.pi μ).map (fun x i => R (x i)) = Measure.pi μ := by
    rw [Measure.pi_map_pi (fun _ => hR.aemeasurable)]
    simp_rw [hμ]
  have ha := ginibreConfigurationOUAssemble_measurable n T
  have hX : Measurable (fun ω i => X i ω) := Measurable.of_eval hm
  have hLaw : P.map (fun ω => ginibreHamiltonianOUJointHorizonPath n α T
      (ginibreHamiltonianOUCoordinateAssembly n (fun i => Z i ω),ginibreBrownianFullContinuousNoise n B α ω)) =
      (Measure.pi μ).map (ginibreConfigurationOUAssemble n T) := by
    rw [Measure.map_congr (ginibreHamiltonianOUReference_horizon_scalar_assembly hn α hα B P hB (fun ω i => Z i ω) T)]
    change P.map ((ginibreConfigurationOUAssemble n T) ∘ (fun ω i => X i ω)) = _
    rw [← Measure.map_map ha hX,hi.map_fun_eq_pi_map (fun i => (hm i).aemeasurable)]
  rw [hLaw]
  have hr : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ),Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)).measurable
  rw [Measure.map_map hr ha]
  change (Measure.pi μ).map (fun x => (ginibreConfigurationOUAssemble n T x).comp
    (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) = _
  have he : (fun x => (ginibreConfigurationOUAssemble n T x).comp
      (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      (ginibreConfigurationOUAssemble n T) ∘ (fun x i => R (x i)) := by
    funext x
    exact (ginibreConfigurationOUAssemble_reverse n T x).symm
  rw [he]
  have hh : Measurable (fun x : (Fin n × Fin 2) → C(Icc (0 : ℝ≥0) T,ℝ) => fun i => R (x i)) :=
    Measurable.of_eval (fun i => hR.comp (measurable_pi_apply i))
  exact (Measure.map_map ha hh).symm.trans (congrArg (Measure.map (ginibreConfigurationOUAssemble n T)) hpi)

theorem ginibreHamiltonian_actual_stationary_killed_action_reverse {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (hα : 0 ≤ α)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (Z : (Fin n × Fin 2) → Ω → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (1/2)) P)
    (hiZ : iIndepFun Z P) (hiB : iIndepFun (fun i ω t => B i t ω) P)
    (hind : IndepFun (fun ω i => Z i ω) (fun ω i t => B i t ω) P) (T : ℝ≥0) (R : ℝ) :
    let μ := P.map (fun ω => ginibreHamiltonianOUJointHorizonPath n α T
      (ginibreHamiltonianOUCoordinateAssembly n (fun i => Z i ω),ginibreBrownianFullContinuousNoise n B α ω))
    (μ.withDensity (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    μ.withDensity (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x)) := by
  dsimp only
  exact invariant_measure_withDensity_of_invariant_weight _ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)).measurable
    (ginibreHamiltonian_actual_stationary_OU_horizon_reverse hn α hα P B hB Z hZ hiZ hiB hind T) _
    (ENNReal.measurable_ofReal.comp (ginibreHamiltonianKilledOUActionWeight_measurable n α (T : ℝ) R T.property))
    (fun x => congrArg ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight_reverse n α (T : ℝ) R T.property x))

#print axioms ginibreHamiltonian_actual_stationary_killed_action_reverse
#print axioms ginibreHamiltonian_actual_stationary_OU_horizon_reverse
end
end GinibrePoincare
