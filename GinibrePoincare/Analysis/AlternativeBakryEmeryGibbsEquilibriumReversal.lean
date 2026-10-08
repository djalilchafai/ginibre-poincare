module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalMixture
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalExhaustion
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalStationaryReference
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance bakryGibbsEquilibrium_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsEquilibrium_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- The literal gradient diffusion path law with its actual Gibbs relative
initial density. Normalization is handled by the concrete initial-law theorem. -/
def bakryEmeryGibbsEquilibriumWeightedPathLaw {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (P : Measure Ω) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) :
    Measure C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  (((Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).prod P).withDensity
    (fun x => ENNReal.ofReal (Real.exp
      (-bakryEmeryGibbsRelativePotential W (ginibreHamiltonianOUCoordinateAssembly n x.1))))).map
    (bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B)

/-- Actual full Gibbs gradient-diffusion reversal. Its killed identities,
stationary Gaussian reference and compact exhaustion are proved internally. -/
theorem bakryEmeryGibbsEquilibriumWeightedPathLaw_reverse {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    (bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)) =
    bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let ν := γ.prod P
  let O := bakryEmeryGibbsGaussianInitialOUPath n T B
  let μ := bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B
  have hO := bakryEmeryGibbsGaussianInitialOUPath_measurable n T B P hB
  apply bakryEmeryGibbs_full_reverse_of_killed_reversals n T μ
  intro k
  have hId := bakryEmeryGibbs_killed_gaussian_initial_identity hn W hW κ hκ hc
    P B hB hiB T hT (k : ℝ)
  change μ.restrict (bakryEmeryGibbsCompactSurvival n T (k : ℝ)) =
    (ν.map O).withDensity (bakryEmeryGibbsKilledOUAction W T (k : ℝ)) at hId
  rw [hId]
  have hRef := bakryEmeryGibbs_completed_product_killed_action_reverse hn W hW P B hB hiB T (k : ℝ)
  have hA : (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν =>
      ginibreHamiltonianOUJointHorizonPath n ((n : ℝ)^2) T
        (ginibreHamiltonianOUCoordinateAssembly n x.1,
          ginibreBrownianFullContinuousNoise n (fun i t y => B i t y.2) ((n : ℝ)^2) x)) =
      (fun x : NullMeasurableSpace (((Fin n × Fin 2) → ℝ) × Ω) ν => O x) := by
    funext x
    rfl
  dsimp only at hRef
  rw [hA,ginibre_map_completion ν O hO] at hRef
  exact hRef

theorem bakryEmeryGibbsEquilibriumWeightedPathLaw_endpoint {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    (bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B).map
      (fun x => x ⟨T,T.property,le_rfl⟩) =
    (bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B).map
      (fun x => x ⟨0,le_rfl,T.property⟩) :=
  ginibreHamiltonian_reversal_endpoint_marginal n T T.property _
    (bakryEmeryGibbsEquilibriumWeightedPathLaw_reverse hn W hW κ hκ hc P B hB hiB T hT)

#print axioms bakryEmeryGibbsEquilibriumWeightedPathLaw_reverse
#print axioms bakryEmeryGibbsEquilibriumWeightedPathLaw_endpoint
end
end GinibrePoincare
