module

public import GinibrePoincare.Analysis.GinibreHamiltonianStateTransitionKernel
public import GinibrePoincare.Analysis.BrownianOrthogonalContinuousPathLaw

@[expose] public section

/-! Exact future laws conditional on arbitrary completed-past random variables. -/
open MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

def ginibreBrownianStateProcess {Ω : Type*} {n : ℕ} (α : ℝ≥0)
    (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    {z : Configuration n // CollisionFree z} :=
  ginibreCanonicalStateValue α t (z,ginibreBrownianFullContinuousNoise n B α ω)

theorem ginibreBrownianStateProcess_adapted {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P) (t : ℝ≥0) :
    @Measurable Ω {z : Configuration n // CollisionFree z}
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _
      (ginibreBrownianStateProcess α z B t) := by
  exact ((ginibreBrownianMaximalProcess_stronglyAdapted hn α z.val B P hB t).measurable).subtype_mk

theorem ginibreBrownian_state_restart_ae {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (hn : 0 < n) (α : ℝ≥0) (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) :
    ginibreBrownianStateProcess α z B (s+t) =ᵐ[P]
      (fun ω => ginibreCanonicalStateValue α t
        (ginibreBrownianStateProcess α z B s ω,
          ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω)) := by
  filter_upwards [ginibreBrownianMaximalProcess_canonical_restart hn α z.val z.property B P hB hind s] with ω hω
  apply Subtype.ext
  exact (hω.2 t).symm

theorem ginibreBrownian_future_past_joint_law {Ω A : Type*} [mAmbient : MeasurableSpace Ω]
    [MeasurableSpace A] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : {z : Configuration n // CollisionFree z})
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal) s) _ Y) :
    P.map (fun ω => (Y ω,ginibreBrownianStateProcess α z B (s+t) ω)) =
      ((P.map (fun ω => (Y ω,ginibreBrownianStateProcess α z B s ω))).prod
        (P.map (ginibreBrownianFullContinuousNoise n B α))).map
          (fun p => (p.1.1,ginibreCanonicalStateValue α t (p.1.2,p.2))) := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let Z := fun ω => (Y ω,ginibreBrownianStateProcess α z B s ω)
  let N := ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α
  have hZpast : @Measurable Ω (A × {z : Configuration n // CollisionFree z}) (F s) _ Z :=
    hY.prodMk (ginibreBrownianStateProcess_adapted hn α z B P hB s)
  have hZa : Measurable Z := hZpast.mono (F.le s) le_rfl
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  have hNa : Measurable N := ginibreBrownianFullContinuousNoise_measurable n _ P hBs α
  have hi := (brownianFamily_future_continuous_noise_independent_augmented_variable
    n B P hB hind α s Z hZpast).symm
  have hLaw := hi.map_prod_eq_prod_map_map hZa.aemeasurable hNa.aemeasurable
  have hg : Measurable (fun p : (A × {z : Configuration n // CollisionFree z}) × GinibreContinuousNoise n =>
      (p.1.1,ginibreCanonicalStateValue α t (p.1.2,p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((ginibreCanonicalStateValue_measurable hn α t).comp
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  rw [← brownianFamily_shift_continuous_noise_law_eq n B P hB hind α s,
    ← hLaw,Measure.map_map hg (hZa.prodMk hNa)]
  apply Measure.map_congr
  filter_upwards [ginibreBrownian_state_restart_ae hn α z B P hB hind s t] with ω hω
  exact congrArg (fun x => (Y ω,x)) hω

end
end GinibrePoincare
