module
public import GinibrePoincare.Analysis.CorrespondenceBrascampLiebWeakTests
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Topology.Algebra.MetricSpace.Lipschitz
@[expose] public section
open MeasureTheory Measure Filter
open scoped ContDiff Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [IsAddHaarMeasure (volume : Measure E)]

 theorem correspondenceBrascampLieb_lipschitz_weak_derivative
    (g : E → ℝ) {C : ℝ≥0} (hg : LipschitzWith C g) (v : E) :
    CorrespondenceBrascampLiebHasWeakDerivative g (fun x => fderiv ℝ g x v) v := by
  intro θ hθ hc
  obtain ⟨D,hD⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hθ (by simp)
  have he := hg.integral_lineDeriv_mul_eq (μ := (volume : Measure E)) hD hc v
  have hl : (∫ x, lineDeriv ℝ g x v*θ x) = ∫ x, θ x*fderiv ℝ g x v := by
    apply integral_congr_ae
    filter_upwards [hg.ae_differentiableAt (μ := (volume : Measure E))] with x hx
    rw [hx.lineDeriv_eq_fderiv]
    ring
  have hr : (∫ x, lineDeriv ℝ θ x (-v)*g x) = -(∫ x, fderiv ℝ θ x v*g x) := by
    rw [← integral_neg]
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      dsimp only
      rw [(hθ.differentiable (by simp) x).lineDeriv_eq_fderiv,map_neg]
      simp
  rw [hl,hr] at he
  exact he

/-- Local Lipschitz functions agree near any prescribed compact set with a
literal global Lipschitz extension. -/
theorem correspondenceBrascampLieb_localLipschitz_extension
    (g : E → ℝ) (hg : LocallyLipschitz g) (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ≥0, ∃ q : E → ℝ, LipschitzWith C q ∧
      ∀ x ∈ K, g =ᶠ[nhds x] q := by
  obtain ⟨R,hR,hbound⟩ := hK.isBounded.exists_pos_norm_le
  obtain ⟨C,hC⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : E) (R+1)) hg.locallyLipschitzOn
  obtain ⟨q,hq,heq⟩ := hC.extend_real
  refine ⟨C,q,hq,?_⟩
  intro x hx
  have hball : x ∈ Metric.ball (0 : E) (R+1) := by
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hbound x hx]
  filter_upwards [Metric.isOpen_ball.mem_nhds hball] with y hy
  exact heq (Metric.ball_subset_closedBall hy)

 theorem correspondenceBrascampLieb_localLipschitz_localL2
    (g : E → ℝ) (hg : LocallyLipschitz g) (v : E) :
    CorrespondenceBrascampLiebLocallyL2 (fun x => fderiv ℝ g x v) := by
  intro K hK
  obtain ⟨C,q,hq,heq⟩ := correspondenceBrascampLieb_localLipschitz_extension g hg K hK
  letI : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hline : MemLp (fun x => lineDeriv ℝ q x v) 2 ((volume : Measure E).restrict K) :=
    (hq.memLp_lineDeriv (μ := (volume : Measure E).restrict K) v).mono_exponent le_top
  have hder : MemLp (fun x => fderiv ℝ q x v) 2 ((volume : Measure E).restrict K) := by
    apply hline.ae_eq
    filter_upwards [ae_restrict_of_ae (hq.ae_differentiableAt (μ := (volume : Measure E)))] with x hx
    exact hx.lineDeriv_eq_fderiv
  apply hder.ae_eq
  apply ae_restrict_of_forall_mem hK.measurableSet
  intro x hx
  exact congrArg (fun L : E →L[ℝ] ℝ => L v) (heq x hx).fderiv_eq.symm

 theorem correspondenceBrascampLieb_localLipschitz_weak_derivative
    (g : E → ℝ) (hg : LocallyLipschitz g) (v : E) :
    CorrespondenceBrascampLiebHasWeakDerivative g (fun x => fderiv ℝ g x v) v := by
  intro θ hθ hc
  obtain ⟨C,q,hq,heq⟩ := correspondenceBrascampLieb_localLipschitz_extension g hg (tsupport θ) hc
  have he := correspondenceBrascampLieb_lipschitz_weak_derivative q hq v θ hθ hc
  have hl : (∫ x, θ x*fderiv ℝ q x v) = ∫ x, θ x*fderiv ℝ g x v := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport θ
      · rw [(heq x hx).fderiv_eq]
      · simp [image_eq_zero_of_notMem_tsupport hx]
  have hr : (∫ x, fderiv ℝ θ x v*q x) = ∫ x, fderiv ℝ θ x v*g x := by
    apply integral_congr_ae
    exact ae_of_all volume fun x => by
      dsimp only
      by_cases hx : x ∈ tsupport θ
      · rw [(heq x hx).eq_of_nhds]
      · rw [fderiv_of_notMem_tsupport ℝ hx]
        simp
  rwa [hl,hr] at he

#print axioms correspondenceBrascampLieb_localLipschitz_localL2
#print axioms correspondenceBrascampLieb_localLipschitz_weak_derivative
end
end GinibrePoincare
