module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionPermutationMean
public import GinibrePoincare.Analysis.GinibreStochasticTransitionBoundedOperator
public import GinibrePoincare.Analysis.GinibreStochasticTransitionResolventOperator

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreOriginalStochasticL2Operator_permute_bounded {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (σ : ParticlePermutation n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : Lp ℝ 2 (ginibreMeasure n)) (v : Configuration n → ℝ)
    (hfv : (f : Configuration n → ℝ)=ᵐ[ginibreMeasure n] v)
    (hv : Measurable v) (C : ℝ) (hC : ∀ z, ‖v z‖≤C) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T (ginibreRealPermutationL2 σ f)=
      ginibreRealPermutationL2 σ (ginibreOriginalStochasticL2Operator hn α P B hB hiB T f) := by
  let A := ginibreOriginalStochasticL2Operator hn α P B hB hiB T
  have hpermuted : (ginibreRealPermutationL2 σ f : Configuration n → ℝ)=ᵐ[ginibreMeasure n]
      (fun z => v (permute σ z)) := by
    have hcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq hfv
    filter_upwards [ginibreRealPermutationL2_ae σ f,hcomp] with z hz hz'
    exact hz.trans hz'
  obtain ⟨hrm,hrb,hr⟩ := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB T
    f v hfv hv C hC
  obtain ⟨hsm,hsb,hs⟩ := ginibreOriginalStochasticL2Operator_bounded_representative hn α P B hB hiB T
    (ginibreRealPermutationL2 σ f) (fun z => v (permute σ z)) hpermuted
    (hv.comp (ginibre_measurePreserving_permute σ).measurable) C (fun z => hC _)
  have hrcomp := (ginibre_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq hr
  apply Lp.ext
  filter_upwards [hs,ginibreRealPermutationL2_ae σ (A f),hrcomp,ginibre_ae_collisionFree n hn]
    with z hz hp hr' hcf
  change (A f) (permute σ z) =
    ginibreStationaryContinuousTransitionMean α B P v T (permute σ z) at hr'
  rw [hz,hp,hr']
  exact ginibreStationaryContinuousTransitionMean_permute hn σ α P B hB hiB v hv T z hcf

theorem ginibreOriginalStochasticL2Operator_permute_symmetric_input {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (σ : ParticlePermutation n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : ginibreFullSymmetricValues n) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T (ginibreRealPermutationL2 σ f.val)=
      ginibreRealPermutationL2 σ (ginibreOriginalStochasticL2Operator hn α P B hB hiB T f.val) := by
  let A := ginibreOriginalStochasticL2Operator hn α P B hB hiB T
  let Q := (ginibreRealPermutationL2 σ).toContinuousLinearMap
  let S := (ginibreFullSymmetricValues n).subtypeL
  have he : A.comp (Q.comp S)=Q.comp (A.comp S) := by
    apply ginibreSymmetricSource_operators_eq_of_bounded_values n
    intro u hu
    obtain ⟨C,hC⟩ := hu
    obtain ⟨v,hv,hvb,hfv⟩ := ginibreBoundedLp_measurable_version hn u.val C hC
    exact ginibreOriginalStochasticL2Operator_permute_bounded hn σ α P B hB hiB T u.val v hfv hv (max C 0) hvb
  exact congrArg (fun L => L f) he

theorem ginibreOriginalStochasticL2Operator_preserves_symmetric {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0)
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i ω t => B i t ω) P) (T : ℝ≥0)
    (f : ginibreFullSymmetricValues n) :
    ginibreOriginalStochasticL2Operator hn α P B hB hiB T f.val ∈ ginibreFullSymmetricValues n := by
  intro σ
  have he := ginibreOriginalStochasticL2Operator_permute_symmetric_input hn σ α P B hB hiB T f
  rw [f.property σ] at he
  exact he.symm

#print axioms ginibreOriginalStochasticL2Operator_preserves_symmetric
end
end GinibrePoincare
