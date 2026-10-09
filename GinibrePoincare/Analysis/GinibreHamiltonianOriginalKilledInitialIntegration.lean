module

public import GinibrePoincare.Analysis.GinibreHamiltonianKilledMixtureIntegration
public import GinibrePoincare.Analysis.GinibreHamiltonianInitialCollisionNormalization
public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltJointCanonicalPath
public import GinibrePoincare.Analysis.GinibreHamiltonianCompletedStationaryReference

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance ginibreOriginalInitialIntegration_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance ginibreOriginalInitialIntegration_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

def ginibreGaussianInitialOriginalPath {Ω : Type*} (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ginibreCanonicalJointHorizonPath α T
    (ginibreInitialCollisionNormalize n (ginibreHamiltonianOUCoordinateAssembly n x.1),
      ginibreBrownianFullContinuousNoise n B α x.2)

def ginibreGaussianInitialOUPath {Ω : Type*} (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (x : ((Fin n × Fin 2) → ℝ) × Ω) :
    C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
  ginibreHamiltonianOUJointHorizonPath n α T
    (ginibreHamiltonianOUCoordinateAssembly n x.1, ginibreBrownianFullContinuousNoise n B α x.2)

theorem ginibreGaussianInitialOriginalPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreGaussianInitialOriginalPath n α T B) :=
  (ginibreCanonicalJointHorizonPath_measurable hn α T).comp
    (((ginibreInitialCollisionNormalize_measurable n).comp
      ((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst)).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

theorem ginibreGaussianInitialOUPath_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (T : ℝ≥0)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (ginibreGaussianInitialOUPath n α T B) :=
  (ginibreHamiltonianOUJointHorizonPath_measurable n α T).comp
    (((ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable.comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

/-- Actual fixed-initial Girsanov laws integrated against the genuine Gaussian
initial law and Vandermonde weight. No stochastic identity is assumed. -/
theorem ginibreHamiltonian_original_killed_gaussian_initial_identity {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
    ((((γ.prod P).withDensity (fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x.1))).map
      (ginibreGaussianInitialOriginalPath n α T B)).restrict (ginibreHamiltonianCompactSurvival n (T : ℝ) R)) =
      ((γ.prod P).map (ginibreGaussianInitialOUPath n α T B)).withDensity
        (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x)) := by
  let γ := Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))
  let C := ginibreGaussianInitialOriginalPath n α T B
  let O := ginibreGaussianInitialOUPath n α T B
  let S := ginibreHamiltonianCompactSurvival n (T : ℝ) R
  let a := fun x => ENNReal.ofReal (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property x)
  let w := fun x => vandermondeDensity (ginibreHamiltonianOUCoordinateAssembly n x)
  let e := fun x => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n (ginibreHamiltonianOUCoordinateAssembly n x)))
  have hC := ginibreGaussianInitialOriginalPath_measurable hn α T B P hB
  have hO := ginibreGaussianInitialOUPath_measurable n α T B P hB
  have hS := ginibreHamiltonianCompactSurvival_measurableSet n (T : ℝ) R
  have ha : Measurable a := ENNReal.measurable_ofReal.comp
    (ginibreHamiltonianOUActionWeight_measurable n α (T : ℝ) T.property)
  have hw : Measurable w := measurable_vandermondeDensity.comp
    (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable
  have he : Measurable e := ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    ((Real.measurable_log.comp (contDiff_vandermondeWeight n).continuous.measurable).neg.comp
      (ginibreHamiltonianOUCoordinateAssembly n).continuous.measurable))
  have hCancel : ∀ᵐ x ∂γ, w x * e x = 1 := by
    filter_upwards [ginibreGaussian_coordinates_collisionFree_ae hn] with x hx
    change ENNReal.ofReal (vandermondeWeight _) * ENNReal.ofReal (Real.exp (ginibreInteractionPotential n _)) = 1
    rw [← ENNReal.ofReal_mul (vandermondeWeight_nonneg _), ginibreInteraction_initial_density_cancellation _ hx]
    norm_num
  have hFiber : ∀ᵐ x ∂γ,
      (P.map (fun ω => C (x, ω))).restrict S =
      (P.withDensity (fun ω => e x * S.indicator a (O (x, ω)))).map (fun ω => O (x, ω)) := by
    filter_upwards [ginibreGaussian_coordinates_collisionFree_ae hn] with x hx
    have h := ginibreBrownian_original_joint_killed_compact_path_law_all_initial hn B P hB hiB α
      (ginibreHamiltonianOUCoordinateAssembly n x) hx R T hT
    have hNorm := ginibreInitialCollisionNormalize_of_free (ginibreHamiltonianOUCoordinateAssembly n x) hx
    have hDensity : (fun ω => ENNReal.ofReal (Real.exp (ginibreInteractionPotential n (ginibreHamiltonianOUCoordinateAssembly n x)) *
        ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property
          (ginibreHamiltonianOUReferenceHorizon n α (ginibreHamiltonianOUCoordinateAssembly n x) B T ω))) =
        (fun ω => e x * S.indicator a (O (x, ω))) := by
      funext ω
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      congr 1
      change ENNReal.ofReal (S.indicator (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property) (O (x, ω))) =
        S.indicator a (O (x, ω))
      by_cases hs : O (x, ω) ∈ S
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
        exact ENNReal.ofReal_zero
    rw [hDensity] at h
    have hOE : ginibreHamiltonianOUReferenceHorizon n α (ginibreHamiltonianOUCoordinateAssembly n x) B T =
        (fun ω => O (x, ω)) := by funext ω; rfl
    rw [hOE] at h
    simpa only [C, ginibreGaussianInitialOriginalPath, hNorm, O, ginibreGaussianInitialOUPath, S,
      ginibreHamiltonianOUReferenceHorizon] using h
  have hMix := ginibre_killed_product_mixture γ P C O hC hO S hS a ha w e hw he hCancel hFiber
  have hKilled : S.indicator a = (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x)) := by
    funext x
    by_cases hx : x ∈ S <;> simp [S, a, ginibreHamiltonianKilledOUActionWeight, hx]
  rw [hKilled] at hMix
  exact hMix

#print axioms ginibreHamiltonian_original_killed_gaussian_initial_identity
end
end GinibrePoincare
