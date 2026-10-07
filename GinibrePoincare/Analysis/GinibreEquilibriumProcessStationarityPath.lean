module

public import GinibrePoincare.Analysis.GinibreEquilibriumProcessStationarityJoint

@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
local instance ginibreStationarityRealPathMeasurable (n:ℕ) : MeasurableSpace C(ℝ,Configuration n) := borel _
local instance ginibreStationarityRealPathBorel (n:ℕ) : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
local instance ginibreStationarityPositivePathMeasurable (n:ℕ) : MeasurableSpace C(ℝ≥0,Configuration n) := borel _
local instance ginibreStationarityPositivePathBorel (n:ℕ) : BorelSpace C(ℝ≥0,Configuration n) := ⟨rfl⟩

def ginibreCanonicalPositivePath {n:ℕ} (α:ℝ)
    (p:{z:Configuration n // CollisionFree z}×GinibreContinuousNoise n) : C(ℝ≥0,Configuration n) :=
  (ginibreDrivenGlobalPathElement α p).comp ⟨fun t=>(t:ℝ),continuous_subtype_val⟩

def ginibreEquilibriumPositivePath {Ω:Type*} {n:ℕ} (α:ℝ≥0)
    (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (p:Configuration n×Ω) : C(ℝ≥0,Configuration n) :=
  ginibreCanonicalPositivePath α (ginibreStationaryFreeInitial n p.1,
    ginibreBrownianFullContinuousNoise n B α p.2)

def ginibreEquilibriumShiftedPositivePath {Ω:Type*} {n:ℕ} (α:ℝ≥0)
    (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (s:ℝ≥0) (p:Configuration n×Ω) : C(ℝ≥0,Configuration n) :=
  (ginibreEquilibriumPositivePath α B p).comp ⟨fun t=>s+t,continuous_const.add continuous_id⟩

theorem ginibreCanonicalPositivePath_measurable {n:ℕ} (hn:0<n) (α:ℝ) :
    Measurable (ginibreCanonicalPositivePath (n:=n) α) :=
  (ContinuousMap.continuous_precomp _).measurable.comp
    (ginibreDrivenGlobalPathElement_measurable hn α)

theorem ginibreEquilibriumPositivePath_measurable {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [P.IsComplete] (hB:∀i,IsBrownianReal (B i) P) :
    Measurable (ginibreEquilibriumPositivePath α B) :=
  (ginibreCanonicalPositivePath_measurable hn α).comp
    (((ginibreStationaryFreeInitial_measurable n).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd))

theorem ginibreEquilibriumShiftedPositivePath_measurable {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [P.IsComplete] (hB:∀i,IsBrownianReal (B i) P) (s:ℝ≥0) :
    Measurable (ginibreEquilibriumShiftedPositivePath α B s) :=
  (ContinuousMap.continuous_precomp _).measurable.comp
    (ginibreEquilibriumPositivePath_measurable hn α B P hB)

theorem ginibreEquilibriumPositivePath_restart_ae {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB:∀i,IsBrownianReal (B i) P) (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) :
    ginibreEquilibriumShiftedPositivePath α B s =ᵐ[(ginibreMeasure n).prod P]
      (fun p=>ginibreCanonicalPositivePath α (ginibreStationaryCurrentState α B s p,
        ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hiB s).1
  have hF := ginibreEquilibriumShiftedPositivePath_measurable hn α B P hB s
  have hG : Measurable (fun p:Configuration n×Ω=>ginibreCanonicalPositivePath α
      (ginibreStationaryCurrentState α B s p,
        ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)) :=
    (ginibreCanonicalPositivePath_measurable hn α).comp
      ((ginibreStationaryCurrentState_measurable hn α B P hB s).prodMk
        ((ginibreBrownianFullContinuousNoise_measurable n _ P hBs α).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hF hG)).mpr
  apply Filter.Eventually.of_forall
  intro z
  let x := ginibreStationaryFreeInitial n z
  filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α x.val x.property B P hB hiB,
    ginibreBrownianMaximalProcess_canonical_restart hn α x.val x.property B P hB hiB s]
    with ω hL hr
  have hL' : ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω).val
      (ginibreStationaryCurrentState α B s (z,ω)).val=⊤ := by
    simpa [ginibreStationaryCurrentState,ginibreBrownianStateProcess,
      ginibreCanonicalStateValue,ginibreBrownianMaximalProcess,x] using hr.1
  apply ContinuousMap.ext
  intro t
  simp only [ginibreEquilibriumShiftedPositivePath,ginibreEquilibriumPositivePath,
    ginibreCanonicalPositivePath,ContinuousMap.comp_apply,ContinuousMap.coe_mk]
  simp only [ginibreDrivenGlobalPathElement,show ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n B α ω).val (ginibreStationaryFreeInitial n z).val=⊤ from hL,
    hL',dif_pos,ContinuousMap.coe_mk,Real.toNNReal_coe]
  simpa [ginibreStationaryCurrentState,ginibreBrownianStateProcess,
    ginibreCanonicalStateValue,ginibreBrownianMaximalProcess,x] using (hr.2 t).symm

theorem ginibreEquilibriumPositivePath_shift_law {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB:∀i,IsBrownianReal (B i) P) (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) :
    ((ginibreMeasure n).prod P).map (ginibreEquilibriumShiftedPositivePath α B s)=
      ((ginibreMeasure n).prod P).map (ginibreEquilibriumPositivePath α B) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hiB s).1
  have hJ := ginibreStationaryCurrentState_future_noise_joint_law hn α B P hB hiB s
  have hN := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  have hNs := ginibreBrownianFullContinuousNoise_measurable n (brownianFamilyShift B s) P hBs α
  have hpair : Measurable (fun p:Configuration n×Ω=>(ginibreStationaryCurrentState α B s p,
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)) :=
    (ginibreStationaryCurrentState_measurable hn α B P hB s).prodMk (hNs.comp measurable_snd)
  rw [Measure.map_congr (ginibreEquilibriumPositivePath_restart_ae hn α B P hB hiB s)]
  change ((ginibreMeasure n).prod P).map
    (ginibreCanonicalPositivePath α ∘ (fun p=>(ginibreStationaryCurrentState α B s p,
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α p.2)))=_
  rw [← Measure.map_map (ginibreCanonicalPositivePath_measurable hn α) hpair,hJ,
    Measure.map_prod_map (ginibreMeasure n) P (ginibreStationaryFreeInitial_measurable n) hN,
    Measure.map_map (ginibreCanonicalPositivePath_measurable hn α)
      ((ginibreStationaryFreeInitial_measurable n).prodMap hN)]
  rfl

theorem ginibreEquilibriumPositivePath_eq_original_ae {Ω:Type*} [MeasurableSpace Ω]
    {n:ℕ} (hn:0<n) (α:ℝ≥0) (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (P:Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB:∀i,IsBrownianReal (B i) P) (hiB:iIndepFun (fun i ω t=>B i t ω) P) :
    ∀ᵐ p:Configuration n×Ω ∂(ginibreMeasure n).prod P,∀t:ℝ≥0,
      ginibreEquilibriumPositivePath α B p t=ginibreBrownianMaximalProcess n α p.1 B t p.2 := by
  filter_upwards [ginibre_equilibrium_path_eq_original hn α (ginibreCollisionFreeDefault n).val
    (ginibreCollisionFreeDefault n).property B P hB hiB] with p hp
  intro t
  simpa [ginibreEquilibriumPositivePath,ginibreCanonicalPositivePath,
    ginibreStationaryFreeInitial,ginibreEquilibriumPath] using hp (t:ℝ)

theorem ginibreBrownian_equilibrium_original_finite_dimensional_stationary
    {Ω ι:Type*} [MeasurableSpace Ω] {n:ℕ} (hn:0<n) (α:ℝ≥0)
    (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P:Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB:∀i,IsBrownianReal (B i) P)
    (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) (t:ι→ℝ≥0) :
    ((ginibreMeasure n).prod P).map
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (s+t i) p.2)=
    ((ginibreMeasure n).prod P).map
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (t i) p.2) := by
  have h := ginibreEquilibriumPositivePath_shift_law hn α B P hB hiB s
  have hEval : Measurable (fun X:C(ℝ≥0,Configuration n)=>fun i=>X (t i)) :=
    Measurable.of_eval (fun i=>(continuous_eval_const _).measurable)
  have hmS := ginibreEquilibriumShiftedPositivePath_measurable hn α B P hB s
  have hm := ginibreEquilibriumPositivePath_measurable hn α B P hB
  have hh := congrArg (fun ν:Measure C(ℝ≥0,Configuration n)=>ν.map
    (fun X=>fun i=>X (t i))) h
  rw [Measure.map_map hEval hmS,Measure.map_map hEval hm] at hh
  have heS : (fun p:Configuration n×Ω=>fun i=>ginibreEquilibriumShiftedPositivePath α B s p (t i))=ᵐ[(ginibreMeasure n).prod P]
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (s+t i) p.2) := by
    filter_upwards [ginibreEquilibriumPositivePath_eq_original_ae hn α B P hB hiB] with p hp
    funext i
    exact hp (s+t i)
  have he : (fun p:Configuration n×Ω=>fun i=>ginibreEquilibriumPositivePath α B p (t i))=ᵐ[(ginibreMeasure n).prod P]
      (fun p=>fun i=>ginibreBrownianMaximalProcess n α p.1 B (t i) p.2) := by
    filter_upwards [ginibreEquilibriumPositivePath_eq_original_ae hn α B P hB hiB] with p hp
    funext i
    exact hp (t i)
  exact (Measure.map_congr heS).symm.trans (hh.trans (Measure.map_congr he))

theorem ginibreBrownian_equilibrium_original_whole_future_stationary
    {Ω:Type*} [MeasurableSpace Ω] {n:ℕ} (hn:0<n) (α:ℝ≥0)
    (B:(Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P:Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB:∀i,IsBrownianReal (B i) P)
    (hiB:iIndepFun (fun i ω t=>B i t ω) P) (s:ℝ≥0) :
    ((ginibreMeasure n).prod P).map
      (fun p=>fun t:ℝ≥0=>ginibreBrownianMaximalProcess n α p.1 B (s+t) p.2)=
    ((ginibreMeasure n).prod P).map
      (fun p=>fun t:ℝ≥0=>ginibreBrownianMaximalProcess n α p.1 B t p.2) :=
  ginibreBrownian_equilibrium_original_finite_dimensional_stationary hn α B P hB hiB s id

#print axioms ginibreBrownian_equilibrium_original_whole_future_stationary

#print axioms ginibreEquilibriumPositivePath_shift_law
#print axioms ginibreBrownian_equilibrium_original_finite_dimensional_stationary

#print axioms ginibreEquilibriumPositivePath_restart_ae
end
end GinibrePoincare
