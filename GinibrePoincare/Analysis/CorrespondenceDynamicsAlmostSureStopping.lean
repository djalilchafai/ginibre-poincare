module
public import GinibrePoincare.Analysis.CorrespondenceDynamicsStrongMarkov
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Almost surely finite stopping times may be made everywhere finite without
changing their stopped past or any of their values off a null event. -/
theorem correspondenceBrownian_ae_finite_stopping
    {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) τ)
    (hf : ∀ᵐ ω ∂P, τ ω ≠ ⊤) :
    ∃ hσ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) (fun ω => ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0)),
      hτ.measurableSpace ≤ hσ.measurableSpace := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have hnull : P {ω | τ ω=⊤} = 0 := by
    simpa only [ae_iff,not_not] using hf
  have hN (s : ℝ≥0) : MeasurableSet[F s] {ω | τ ω=⊤} :=
    ginibreNullAugmentation_null_measurable P _ _ hnull
  have he (s : ℝ≥0) : {ω | ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0) ≤ s} =
      {ω | τ ω≤s} ∪ {ω | τ ω=⊤} := by
    ext ω
    cases h : τ ω with
    | top => simp [h,WithTop.untopD_top,WithTop.coe_le_coe,show (0 : ℝ≥0) ≤ s from bot_le]
    | coe t =>
      simp only [mem_setOf_eq,mem_union,h]
      rw [WithTop.untopD_coe (0 : ℝ≥0) t]
      simp only [WithTop.coe_ne_top,or_false]
  have hσ : IsStoppingTime F (fun ω => ((WithTop.untopD (0 : ℝ≥0) (τ ω) : ℝ≥0) : WithTop ℝ≥0)) := by
    intro s
    rw [he s]
    exact (hτ s).union (hN s)
  refine ⟨hσ,?_⟩
  intro A hA
  have hh := (hτ.measurableSet A).mp hA
  apply (hσ.measurableSet A).mpr
  refine ⟨hh.1,fun s => ?_⟩
  rw [he s,inter_union_distrib_left]
  have hn : P (A ∩ {ω | τ ω=⊤}) = 0 :=
    measure_mono_null inter_subset_right hnull
  exact (hh.2 s).union (ginibreNullAugmentation_null_measurable P _ _ hn)

theorem correspondence_ginibre_ae_finite_strongMarkov
    {Ω A : Type*} [mAmbient : MeasurableSpace Ω] [MeasurableSpace A]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (τ : Ω → WithTop ℝ≥0)
    (hτ : IsStoppingTime (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)) τ)
    (hf : ∀ᵐ ω ∂P, τ ω ≠ ⊤)
    (t : ℝ≥0) (Y : Ω → A) (hY : @Measurable Ω A hτ.measurableSpace _ Y) :
    P.map (fun ω => (Y ω,ginibreBrownianStateProcess α z B (WithTop.untopD (0 : ℝ≥0) (τ ω)+t) ω)) =
      ((P.map (fun ω => (Y ω,ginibreBrownianStateProcess α z B (WithTop.untopD (0 : ℝ≥0) (τ ω)) ω))).prod
        (P.map (ginibreBrownianFullContinuousNoise n B α))).map
          (fun p => (p.1.1,ginibreCanonicalStateValue α t (p.1.2,p.2))) := by
  obtain ⟨hσ,hle⟩ := correspondenceBrownian_ae_finite_stopping n B P hB τ hτ hf
  exact correspondence_ginibre_stopping_future_past_joint_law hn α z B P hB hind
    (fun ω => WithTop.untopD (0 : ℝ≥0) (τ ω)) hσ t Y (hY.mono hle le_rfl)

#print axioms correspondence_ginibre_ae_finite_strongMarkov

#print axioms correspondenceBrownian_ae_finite_stopping
end
end GinibrePoincare
