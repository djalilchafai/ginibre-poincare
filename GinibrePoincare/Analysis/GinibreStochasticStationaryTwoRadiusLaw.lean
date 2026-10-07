module

public import GinibrePoincare.Analysis.GinibreTwoRadiusEquilibriumLaw
public import GinibrePoincare.Analysis.GinibreHamiltonianOriginalEquilibriumMarginals

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance ginibreStationaryTwoRadiusPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := borel _
local instance ginibreStationaryTwoRadiusPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := ⟨rfl⟩

/-- Both actual original equilibrium CIR observables have the exact independent
Gamma joint law at every time, including zero speed and zero horizon. -/
theorem ginibreOriginalEquilibrium_two_radius_gamma_product {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => (ginibreCenterSquared n (x ⟨T,T.property,le_rfl⟩),
        pairwiseRadius (x ⟨T,T.property,le_rfl⟩))) =
      (gammaMeasure 1 1).prod (gammaMeasure (recenteredGammaShape n : ℝ) 1) := by
  have hm : Measurable (fun z : Configuration n => (ginibreCenterSquared n z,pairwiseRadius z)) := by
    unfold ginibreCenterSquared pairwiseRadius coordinateSum
    fun_prop
  have he : Measurable (fun x : C(Icc (0 : ℝ) (T : ℝ),Configuration n) => x ⟨T,T.property,le_rfl⟩) :=
    (continuous_eval_const _).measurable
  have hl := ginibreOriginalEquilibriumPathLaw_terminal (by omega : 0<n) α P B hB hiB T
  have h := congrArg (fun ν : Measure (Configuration n) =>
    ν.map (fun z => (ginibreCenterSquared n z,pairwiseRadius z))) hl
  rw [Measure.map_map hm he,ginibreTwoRadius_equilibrium_gamma_product n hn] at h
  exact h

#print axioms ginibreOriginalEquilibrium_two_radius_gamma_product
end
end GinibrePoincare
