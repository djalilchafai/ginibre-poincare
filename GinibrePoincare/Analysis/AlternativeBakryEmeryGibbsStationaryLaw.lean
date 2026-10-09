module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsInitialLaw
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsEquilibriumReversal
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
local instance bakryStationaryLaw_configMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryStationaryLaw_configBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩
local instance bakryStationaryLaw_euclideanMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) := borel _
local instance bakryStationaryLaw_euclideanBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), EuclideanSpace ℝ (Fin n × Fin 2)) := ⟨rfl⟩

def bakryEmeryGibbsActualEndpoint {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (p : Configuration n × Ω) :
    Configuration n :=
  bakryEmeryGibbsPath W hW κ hκ hc T (p.1, bakryEmeryOriginalCompactDriver n B T p.2)
    ⟨T, T.coe_nonneg, le_rfl⟩

theorem bakryEmeryGibbsActualEndpoint_measurable {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (T : ℝ≥0) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) :
    Measurable (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B) := by
  let pth := bakryEmeryGibbsPath W hW κ hκ hc T
  have hm : Measurable pth := bakryEmeryGibbsPath_measurable W hW κ hκ hc T
  have hn := bakryEmeryOriginalCompactDriver_measurable n B P hB T
  have hi : Measurable (fun p : Configuration n × Ω =>
      (p.1, bakryEmeryOriginalCompactDriver n B T p.2)) :=
    measurable_fst.prodMk (hn.comp measurable_snd)
  have he : Measurable (fun q : C(Icc (0 : ℝ) (T : ℝ), Configuration n) =>
      q ⟨(T : ℝ), T.coe_nonneg, le_rfl⟩) := ContinuousMap.measurable_eval _
  change Measurable (fun p : Configuration n × Ω =>
    pth (p.1, bakryEmeryOriginalCompactDriver n B T p.2) ⟨(T : ℝ), T.coe_nonneg, le_rfl⟩)
  exact he.comp (hm.comp hi)

/-- The literal Gibbs law is invariant for the actual unit-diffusion gradient
endpoint, with both the solution factory and Gibbs mass discharged internally. -/
theorem bakryEmeryGibbsActualEndpoint_stationary {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    ((bakryEmeryNormalizedGibbs volume W).prod P).map
      (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B) = bakryEmeryNormalizedGibbs volume W := by
  let A := ginibreHamiltonianOUCoordinateAssembly n
  let σ := bakryEmeryGibbsCoordinateRawMeasure n W
  let σN := bakryEmeryGibbsCoordinateInitialMeasure n W
  let F := bakryEmeryGibbsGaussianInitialPath W hW κ hκ hc T B
  let E := bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B
  have hA : Measurable A := A.continuous.measurable
  have hF := bakryEmeryGibbsGaussianInitialPath_measurable W hW κ hκ hc T B P hB
  have hE := bakryEmeryGibbsActualEndpoint_measurable W hW κ hκ hc T B P hB
  have hw : Measurable (bakryEmeryGibbsCoordinateWeight n W) := by
    have hS : Continuous (bakryEmeryGibbsRelativePotential W) :=
      hW.continuous.sub (continuous_const.mul contDiff_configurationNormSq.continuous)
    exact (ENNReal.measurable_ofReal.comp (Real.continuous_exp.comp hS.neg).measurable).comp hA
  have hraw : bakryEmeryGibbsEquilibriumWeightedPathLaw W hW κ hκ hc T P B = (σ.prod P).map F := by
    unfold bakryEmeryGibbsEquilibriumWeightedPathLaw
    change (((Measure.pi (fun _ : Fin n × Fin 2 => gaussianReal 0 (1/2))).prod P).withDensity
      (fun x => bakryEmeryGibbsCoordinateWeight n W x.1)).map F = _
    rw [← prod_withDensity_left hw]
    rfl
  have hEnd := bakryEmeryGibbsEquilibriumWeightedPathLaw_endpoint hn W hW κ hκ hc P B hB hiB T hT
  rw [hraw, Measure.map_map (ContinuousMap.measurable_eval _) hF,
    Measure.map_map (ContinuousMap.measurable_eval _) hF] at hEnd
  have hinit : (fun x => F x ⟨0, le_rfl, T.coe_nonneg⟩) = A ∘ Prod.fst := by
    funext x
    exact bakryEmeryGibbsGaussianInitialPath_initial W hW κ hκ hc T B x
  have hterm : (fun x => F x ⟨T, T.coe_nonneg, le_rfl⟩) = E ∘ Prod.map A id := by rfl
  change (σ.prod P).map (fun x => F x ⟨T, T.coe_nonneg, le_rfl⟩) =
    (σ.prod P).map (fun x => F x ⟨0, le_rfl, T.coe_nonneg⟩) at hEnd
  rw [hinit,← Measure.map_map hA measurable_fst, Measure.map_fst_prod, measure_univ, one_smul] at hEnd
  have hσN : IsProbabilityMeasure σN := bakryEmeryGibbsCoordinateInitialMeasure_probability hn W hW κ hκ hc
  letI := hσN
  have hassembly : σN.map A = bakryEmeryNormalizedGibbs volume W :=
    bakryEmeryGibbsCoordinateInitialMeasure_assembly hn W hW κ hκ hc
  have hprod : (σN.map A).prod P = (σN.prod P).map (Prod.map A id) := by
    simpa using Measure.map_prod_map σN P hA measurable_id
  rw [← hassembly, hprod, Measure.map_map hE (hA.prodMap measurable_id)]
  change (σN.prod P).map (E ∘ Prod.map A id) = σN.map A
  rw [← hterm]
  unfold σN bakryEmeryGibbsCoordinateInitialMeasure
  have hTerm : Measurable (fun x : ((Fin n × Fin 2) → ℝ) × Ω => F x
      (⟨(T : ℝ), T.coe_nonneg, le_rfl⟩ : Icc (0 : ℝ) (T : ℝ))) :=
    (ContinuousMap.measurable_eval (⟨(T : ℝ), T.coe_nonneg, le_rfl⟩ : Icc (0 : ℝ) (T : ℝ))).comp hF
  rw [Measure.prod_smul_left, Measure.map_smul _ hTerm.aemeasurable,
    Measure.map_smul _ hA.aemeasurable]
  exact congrArg (fun μ => (bakryEmeryGibbsCoordinateRawMeasure n W univ)⁻¹ • μ) hEnd


/-- The same concrete stationary endpoint law in the real Hilbert coordinates
used for the Bakry–Émery contraction and entropy proof. -/
theorem bakryEmeryGibbsActualEndpoint_hilbert_stationary {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0) (hT : 0 < T) :
    ((bakryEmeryNormalizedGibbs volume W).prod P).map
      (fun p => configurationEuclideanEquiv n (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B p)) =
      bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm) := by
  have hh := congrArg (Measure.map (configurationEuclideanEquiv n))
    (bakryEmeryGibbsActualEndpoint_stationary hn W hW κ hκ hc P B hB hiB T hT)
  rw [Measure.map_map (configurationEuclideanEquiv n).continuous.measurable
    (bakryEmeryGibbsActualEndpoint_measurable W hW κ hκ hc T B P hB),
    bakryEmeryConfiguration_normalizedGibbs_map n W hW.continuous] at hh
  exact hh

#print axioms bakryEmeryGibbsActualEndpoint_hilbert_stationary
#print axioms bakryEmeryGibbsActualEndpoint_measurable
#print axioms bakryEmeryGibbsActualEndpoint_stationary
end
end GinibrePoincare
