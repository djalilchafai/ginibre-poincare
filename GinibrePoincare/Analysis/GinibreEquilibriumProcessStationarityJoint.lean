module

public import GinibrePoincare.Analysis.GinibreHamiltonianMarkovLaw
public import GinibrePoincare.Analysis.GinibreHamiltonianEquilibriumProductLaw
public import GinibrePoincare.Analysis.IndependentNoiseMixture

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

def ginibreStationaryFreeInitial (n:ℕ) : Configuration n→{z:Configuration n // CollisionFree z} :=
  ginibreFreeInitialVersion (ginibreCollisionFreeDefault n).val (ginibreCollisionFreeDefault n).property

def ginibreStationaryCurrentState {Ω:Type*} {n:ℕ} (α:ℝ≥0)
    (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (s:ℝ≥0) (p:Configuration n×Ω) :
    {z:Configuration n // CollisionFree z} :=
  ginibreBrownianStateProcess α (ginibreStationaryFreeInitial n p.1) B s p.2

theorem ginibreStationaryFreeInitial_measurable (n:ℕ) : Measurable (ginibreStationaryFreeInitial n) :=
  ginibreFreeInitialVersion_measurable _ _

theorem ginibreStationaryCurrentState_measurable {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [P.IsComplete] (hB:∀i,IsBrownianReal (B i) P) (s:ℝ≥0) :
    Measurable (ginibreStationaryCurrentState α B s) :=
  (ginibreCanonicalStateValue_measurable hn α s).comp
    (((ginibreStationaryFreeInitial_measurable n).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

theorem ginibreStationaryCurrentState_value_law {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB:∀i,IsBrownianReal (B i) P) (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) :
    ((ginibreMeasure n).prod P).map (fun p=>(ginibreStationaryCurrentState α B s p).val)=ginibreMeasure n := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hcf : ∀ᵐ p:Configuration n×Ω ∂(ginibreMeasure n).prod P,CollisionFree p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_collisionFree n).measurableSet.preimage measurable_fst)).mpr
    exact (ginibre_ae_collisionFree n hn).mono fun z hz=>Filter.Eventually.of_forall fun _=>hz
  have he : (fun p=>(ginibreStationaryCurrentState α B s p).val)=ᵐ[(ginibreMeasure n).prod P]
      (fun p=>ginibreBrownianMaximalProcess n α p.1 B s p.2) := by
    filter_upwards [hcf] with p hp
    simp [ginibreStationaryCurrentState,ginibreStationaryFreeInitial,ginibreBrownianStateProcess,
      ginibreCanonicalStateValue,ginibreFreeInitialVersion,hp,ginibreBrownianMaximalProcess]
  rw [Measure.map_congr he]
  exact ginibreBrownian_equilibrium_original_invariant hn α P B hB hiB s

theorem ginibreStationaryCurrentState_law {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB:∀i,IsBrownianReal (B i) P) (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) :
    ((ginibreMeasure n).prod P).map (ginibreStationaryCurrentState α B s)=
      (ginibreMeasure n).map (ginibreStationaryFreeInitial n) := by
  have hx := ginibreStationaryCurrentState_measurable hn α B P hB s
  have hv := ginibreStationaryCurrentState_value_law hn α B P hB hiB s
  conv_rhs => rw [← hv]
  rw [Measure.map_map (ginibreStationaryFreeInitial_measurable n)
    (show Measurable (fun p=>(ginibreStationaryCurrentState α B s p).val) from measurable_subtype_coe.comp hx)]
  congr 1
  funext p
  simp [ginibreStationaryFreeInitial,ginibreFreeInitialVersion,
    (ginibreStationaryCurrentState α B s p).property]

theorem ginibreStationaryCurrentState_future_noise_joint_law {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB:∀i,IsBrownianReal (B i) P) (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) :
    ((ginibreMeasure n).prod P).map (fun p=>(ginibreStationaryCurrentState α B s p,
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2))=
      ((ginibreMeasure n).map (ginibreStationaryFreeInitial n)).prod
        (P.map (ginibreBrownianFullContinuousNoise n B α)) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hiB s).1
  have hN := ginibreBrownianFullContinuousNoise_measurable n (brownianFamilyShift B s) P hBs α
  have hmix := independentNoiseMixture_joint_law (ginibreMeasure n) P
    (ginibreStationaryCurrentState α B s)
    (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α)
    (ginibreStationaryCurrentState_measurable hn α B P hB s) hN
    (fun z=>by
      have hx := ginibreBrownianStateProcess_adapted hn α (ginibreStationaryFreeInitial n z) B P hB s
      have hi := (brownianFamily_future_continuous_noise_independent_augmented_variable
        n B P hB hiB α s (ginibreBrownianStateProcess α (ginibreStationaryFreeInitial n z) B s) hx).symm
      exact hi.map_prod_eq_prod_map_map
        (hx.mono ((ginibreBrownianAugmentedFiltration B P (fun i=>(hB i).toIsPreBrownianReal)).le s) le_rfl).aemeasurable
        hN.aemeasurable)
  rw [ginibreStationaryCurrentState_law hn α B P hB hiB s,
    brownianFamily_shift_continuous_noise_law_eq n B P hB hiB α s] at hmix
  exact hmix

#print axioms ginibreStationaryCurrentState_future_noise_joint_law
end
end GinibrePoincare
