module

public import GinibrePoincare.Analysis.PairwiseRadius
public import GinibrePoincare.Analysis.GinibreStochasticNoncollision
public import GinibrePoincare.Analysis.BrownianOrthogonalRadialFrame
public import GinibrePoincare.Analysis.GaussianFourierCoordinates
public import GinibrePoincare.Analysis.GinibreDrivenPathFactorization

@[expose] public section

/-! The actual recentered path has a continuous unit radial direction: collision
freeness, rather than an assumed radial positivity certificate, excludes zero. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem recenteredConfiguration_ne_zero_of_collisionFree {n : ℕ} (hn : 2 ≤ n)
    (z : Configuration n) (hz : CollisionFree z) : recenteredConfiguration n z ≠ 0 := by
  intro h
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hi := congrFun h i
  have hj := congrFun h j
  have he : z i = z j := by
    simp only [recenteredConfiguration,projectToOrthogonal,Pi.zero_apply] at hi hj
    exact sub_eq_zero.mp hi |>.trans (sub_eq_zero.mp hj).symm
  have hij : i ≠ j := by simp [i,j,Fin.ext_iff]
  exact hij (hz he)

theorem pairwiseRadius_pos_of_collisionFree {n : ℕ} (hn : 2 ≤ n)
    (z : Configuration n) (hz : CollisionFree z) : 0 < pairwiseRadius z := by
  classical
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i ≠ j := by simp [i,j,Fin.ext_iff]
  have hzj : z i-z j ≠ 0 := sub_ne_zero.mpr (fun h => hij (hz h))
  unfold pairwiseRadius
  apply Finset.sum_pos'
  · intro k hk
    exact Finset.sum_nonneg (fun l hl => Complex.normSq_nonneg _)
  · refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.sum_pos'
    · intro k hk
      exact Complex.normSq_nonneg _
    · exact ⟨j,Finset.mem_Ioi.mpr (by simp [i,j]),Complex.normSq_pos.mpr hzj⟩

theorem brownianRadialUnitVector_continuousAt {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (x e : E) (hx : x ≠ 0) :
    ContinuousAt (fun y => brownianRadialUnitVector y e) x := by
  have he : (fun y => brownianRadialUnitVector y e) =ᶠ[nhds x]
      (fun y => ‖y‖⁻¹ • y) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff] at hy
    simp [brownianRadialUnitVector,hy]
  exact ((continuous_norm.continuousAt.inv₀ (norm_ne_zero_iff.mpr hx)).smul
    continuousAt_id).congr he.symm

def ginibreRecenteredRadialDirection (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  brownianRadialUnitVector (configurationEuclideanEquiv n (recenteredConfiguration n z)) e

theorem ginibreRecenteredRadialDirection_norm (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖=1) (z : Configuration n) :
    ‖ginibreRecenteredRadialDirection n e z‖=1 :=
  brownianRadialUnitVector_norm _ e he

theorem ginibreRecenteredRadialDirection_measurable (n : ℕ)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) :
    Measurable (ginibreRecenteredRadialDirection n e) := by
  exact (brownianRadialUnitVector_measurable e).comp
    ((configurationEuclideanEquiv n).continuous.measurable.comp (by
      simpa only [recenteredCLM_apply] using (show Measurable (fun x => recenteredCLM n x) from (recenteredCLM n).measurable)))

theorem ginibreRecenteredRadialDirection_continuousAt {n : ℕ} (hn : 2 ≤ n)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (z : Configuration n) (hz : CollisionFree z) :
    ContinuousAt (ginibreRecenteredRadialDirection n e) z := by
  have hne : configurationEuclideanEquiv n (recenteredConfiguration n z) ≠ 0 := by
    intro h
    apply recenteredConfiguration_ne_zero_of_collisionFree hn z hz
    exact (configurationEuclideanEquiv n).injective (by simpa using h)
  have hr : ContinuousAt (recenteredConfiguration n) z := by
    simpa only [recenteredCLM_apply] using (show ContinuousAt (fun x => recenteredCLM n x) z from (recenteredCLM n).continuous.continuousAt)
  have hc : ContinuousAt (fun x => configurationEuclideanEquiv n (recenteredConfiguration n x)) z :=
    (configurationEuclideanEquiv n).continuous.continuousAt.comp hr
  exact (brownianRadialUnitVector_continuousAt _ e hne).comp (f := fun x => configurationEuclideanEquiv n (recenteredConfiguration n x)) hc

theorem ginibreBrownianMaximalProcess_radialDirection_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (he : ‖e‖=1) :
    let u := fun t ω => ginibreRecenteredRadialDirection n e
      (ginibreBrownianMaximalProcess n α z B t ω)
    (∀ t, @Measurable Ω (EuclideanSpace ℝ (Fin n × Fin 2))
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) t) _ (u t)) ∧
    (∀ t ω, ‖u t ω‖=1) ∧ (∀ᵐ ω ∂P, Continuous (fun t => u t ω)) := by
  dsimp only
  obtain ⟨hAdapt,hPath⟩ := ginibreBrownianMaximalProcess_global_original_solution
    (by omega) α z hz B P hB hind
  refine ⟨fun t => (ginibreRecenteredRadialDirection_measurable n e).comp
    (hAdapt t).measurable,fun t ω => ginibreRecenteredRadialDirection_norm n e he _,?_⟩
  filter_upwards [hPath] with ω hω
  have hX : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
    simpa only [Real.toNNReal_coe] using (show Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B (t : ℝ).toNNReal ω) from hω.1.comp NNReal.continuous_coe)
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (ginibreRecenteredRadialDirection_continuousAt hn e _
    (by simpa only [Real.toNNReal_coe] using hω.2.2.1 t t.coe_nonneg)).comp
    (f := fun s : ℝ≥0 => ginibreBrownianMaximalProcess n α z B s ω) hX.continuousAt

end
end GinibrePoincare
