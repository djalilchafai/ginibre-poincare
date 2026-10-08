module
public import GinibrePoincare.Analysis.CorrespondenceOperatorMartingaleApproximation
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-- The actual original global Ginibre diffusion solves the full compact-test
martingale problem in its genuine completed Brownian filtration. The literal
unlocalized differential-generator deficit itself is a martingale. -/
theorem correspondenceOperator_global_martingale_problem
    {Ω : Type*} [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0<n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀i,IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n→ℝ) (hf : IsGinibreCollisionFreeCompactTest f) :
    Martingale (correspondenceOperator_test_deficit n α z B f)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P := by
  let D := correspondenceOperator_test_deficit n α z B f
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  have had : StronglyAdapted F D := by
    intro r
    obtain ⟨M,C,hM,hbound,hlim⟩ := correspondenceOperator_martingale_approximation
      hn α z hz B P hB hind f hf r
    have hs : StronglyMeasurable[F r] (fun ω => limUnder atTop (fun m => M m r ω)) := by
      letI : MeasurableSpace Ω := F r
      exact StronglyMeasurable.limUnder (fun m => (hM m).stronglyAdapted r)
    have hae : (fun ω => limUnder atTop (fun m => M m r ω))=ᵐ[P] D r := by
      filter_upwards [hlim r le_rfl] with ω hω
      exact hω.limUnder_eq
    have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) r
    let mPast := ginibreBrownianFamilyPastSpace B r
    let hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
    let μ := P.trim hAug
    haveI : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
    have hae' := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _ hae
    exact ((aemeasurable_iff_measurable (μ := μ)).mp
      (hs.measurable.aemeasurable.congr hae')).stronglyMeasurable
  have hi (r : ℝ≥0) : Integrable (D r) P := by
    obtain ⟨M,C,hM,hbound,hlim⟩ := correspondenceOperator_martingale_approximation
      hn α z hz B P hB hind f hf r
    have hb : ∀ᵐ ω ∂P,‖D r ω‖≤C := by
      filter_upwards [hlim r le_rfl,ae_all_iff.mpr (fun m => hbound m r le_rfl)] with ω hω hb
      exact le_of_tendsto hω.norm (Eventually.of_forall hb)
    exact (integrable_const C).mono' ((had r).mono (F.le r)).aestronglyMeasurable hb
  refine ⟨had,fun s t hst => ?_⟩
  apply (ae_eq_condExp_of_forall_setIntegral_eq (F.le s) (hi t)
    (fun _ _ _ => (hi s).integrableOn) ?_ (had s).aestronglyMeasurable).symm
  intro A hA _
  obtain ⟨M,C,hM,hbound,hlim⟩ := correspondenceOperator_martingale_approximation
    hn α z hz B P hB hind f hf t
  have hI (r : ℝ≥0) (hr : r≤t) : Tendsto (fun m => ∫ ω in A,M m r ω ∂P)
      atTop (𝓝 (∫ ω in A,D r ω ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ : Ω => C)
    · intro m
      exact ((hM m).integrable r).aestronglyMeasurable.mono_measure Measure.restrict_le_self
    · exact integrable_const C
    · intro m
      exact ae_restrict_of_ae (hbound m r hr)
    · exact ae_restrict_of_ae (hlim r hr)
  have he (m : ℕ) : (∫ ω in A,M m s ω ∂P)=∫ ω in A,M m t ω ∂P :=
    (hM m).setIntegral_eq hst hA
  exact tendsto_nhds_unique (hI s hst) ((hI t le_rfl).congr (fun m => (he m).symm))
#print axioms correspondenceOperator_global_martingale_problem
end
end GinibrePoincare
