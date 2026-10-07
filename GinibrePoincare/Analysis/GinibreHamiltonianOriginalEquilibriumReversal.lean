module

public import GinibrePoincare.Analysis.GinibreHamiltonianOriginalKilledInitialIntegration
public import GinibrePoincare.Analysis.GinibreHamiltonianKilledExhaustionIntegration
public import GinibrePoincare.Analysis.GinibreHamiltonianReversalMarginals

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance ginibreOriginalEquilibrium_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := borel _
local instance ginibreOriginalEquilibrium_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := ⟨rfl⟩

/-- The genuine canonical original Ginibre path with independently sampled
Gaussian coordinates and original Brownian noise, weighted by the actual
normalized Vandermonde initial density. -/
def ginibreOriginalEquilibriumPathLaw {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (T : ℝ≥0) (P : Measure Ω)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) :
    Measure C(Icc (0 : ℝ) (T : ℝ),Configuration n) :=
  (ginibreNormalizingMass n)⁻¹ •
    (((Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).prod P).withDensity
      (fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))).map
      (ginibreGaussianInitialOriginalPath n α T B)

/-- Actual full original Ginibre equilibrium path-law reversal, derived from
bounded Girsanov on Hamiltonian sublevels, true stationary OU reversal, exact
Gaussian/Ginibre initial cancellation and countable sublevel exhaustion. -/
theorem ginibreOriginalEquilibriumPathLaw_reverse {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    (ginibreOriginalEquilibriumPathLaw n α T P B).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      ginibreOriginalEquilibriumPathLaw n α T P B := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let ν := γ.prod P
  let C := ginibreGaussianInitialOriginalPath n α T B
  let O := ginibreGaussianInitialOUPath n α T B
  let μ := (ν.withDensity (fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))).map C
  have hC := ginibreGaussianInitialOriginalPath_measurable hn α T B P hB
  have hO := ginibreGaussianInitialOUPath_measurable n α T B P hB
  have hCFset : MeasurableSet {x : C(Icc (0 : ℝ) (T : ℝ),Configuration n) | ∀ t, CollisionFree (x t)} := by
    have he : {x : C(Icc (0 : ℝ) (T : ℝ),Configuration n) | ∀ t, CollisionFree (x t)} =
        ⋃ k : ℕ, ginibreHamiltonianCompactSurvival n (T : ℝ) (k : ℝ) := by
      ext x
      simp only [Set.mem_setOf_eq,Set.mem_iUnion,ginibreHamiltonianCompactSurvival,Set.mem_setOf_eq]
      exact (ginibreHamiltonian_compact_path_survival_exhaustion_iff (T : ℝ) x).symm
    rw [he]
    exact MeasurableSet.iUnion (fun k => ginibreHamiltonianCompactSurvival_measurableSet n (T : ℝ) k)
  have hCF : ∀ᵐ x ∂μ, ∀ t, CollisionFree (x t) := by
    apply (ae_map_iff hC.aemeasurable hCFset).mpr
    exact Filter.Eventually.of_forall (fun x t =>
      ginibreCanonicalJointHorizonPath_collisionFree α T _ t)
  have hKilled (k : ℕ) :
      (μ.restrict (ginibreHamiltonianCompactSurvival n (T : ℝ) (k : ℝ))).map
        (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
      μ.restrict (ginibreHamiltonianCompactSurvival n (T : ℝ) (k : ℝ)) := by
    have hId := ginibreHamiltonian_original_killed_gaussian_initial_identity hn α P B hB hiB T hT (k : ℝ)
    change μ.restrict (ginibreHamiltonianCompactSurvival n (T : ℝ) (k : ℝ)) =
      (ν.map O).withDensity (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) (k : ℝ) T.property x)) at hId
    rw [hId]
    have hRef := ginibreHamiltonian_completed_product_killed_action_reverse hn α α.property P B hB hiB T (k : ℝ)
    have hA : (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
        ginibreHamiltonianOUJointHorizonPath n α T
          (ginibreHamiltonianOUCoordinateAssembly n x.1,
            ginibreBrownianFullContinuousNoise n (fun i t y => B i t y.2) α x)) =
        (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν => O x) := by
      funext x
      rfl
    dsimp only at hRef
    rw [hA,ginibre_map_completion ν O hO] at hRef
    exact hRef
  have hFull := ginibreHamiltonian_full_reverse_of_actual_killed_reversals n (T : ℝ) T.property μ hCF hKilled
  unfold ginibreOriginalEquilibriumPathLaw
  rw [Measure.map_smul _ (ContinuousMap.continuous_precomp
    (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)).measurable.aemeasurable]
  exact congrArg (fun η => (ginibreNormalizingMass n)⁻¹ • η) hFull

#print axioms ginibreOriginalEquilibriumPathLaw_reverse
end
end GinibrePoincare
