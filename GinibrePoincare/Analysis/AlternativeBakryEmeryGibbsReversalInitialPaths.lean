module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalPathFactory
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinCorrectedDriver
public import GinibrePoincare.Analysis.GinibreHamiltonianActualStationaryOUReversal
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance bakryGibbsInitialPaths_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsInitialPaths_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Actual gradient diffusion driven by the original Brownian coordinates,
with its initial state supplied by the concrete Gaussian coordinate assembly. -/
def bakryEmeryGibbsGaussianInitialPath {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (x : ((Fin n × Fin 2) → ℝ) × Ω) : C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  bakryEmeryGibbsPath W hW κ hκ hc T
    (ginibreHamiltonianOUCoordinateAssembly n x.1, bakryEmeryOriginalCompactDriver n B T x.2)

def bakryEmeryGibbsGaussianInitialOUPath {Ω : Type*} (n : ℕ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (x : ((Fin n × Fin 2) → ℝ) × Ω) : C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ginibreHamiltonianOUJointHorizonPath n ((n : ℝ)^2) T
    (ginibreHamiltonianOUCoordinateAssembly n x.1,
      ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) x.2)

theorem bakryEmeryGibbsGaussianInitialPath_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B) :=
  (bakryEmeryGibbsPath_measurable W hW κ hκ hc T).comp
    (((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst).prodMk
      ((bakryEmeryOriginalCompactDriver_measurable n B P hB T).comp measurable_snd))

theorem bakryEmeryGibbsGaussianInitialOUPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryGibbsGaussianInitialOUPath n T B) :=
  (ginibreHamiltonianOUJointHorizonPath_measurable n ((n : ℝ)^2) T).comp
    (((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB ((n : ℝ)^2)).comp measurable_snd))

@[simp] theorem bakryEmeryGibbsGaussianInitialPath_initial {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B x ⟨0, le_rfl, T.property⟩ =
      ginibreHamiltonianOUCoordinateAssembly n x.1 := by
  unfold bakryEmeryGibbsGaussianInitialPath
  rw [bakryEmeryGibbsPath_initial]
  have hzero := (ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) x.2).property
  change _ + (configurationEuclideanEquiv n).symm
    ((configurationEuclideanEquiv n) ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) x.2).val 0)) = _
  rw [hzero]
  simp

#print axioms bakryEmeryGibbsGaussianInitialPath_initial
#print axioms bakryEmeryGibbsGaussianInitialPath_measurable
#print axioms bakryEmeryGibbsGaussianInitialOUPath_measurable
end
end GinibrePoincare
