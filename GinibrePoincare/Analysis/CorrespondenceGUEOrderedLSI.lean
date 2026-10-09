module
public import GinibrePoincare.Analysis.CorrespondenceGUEExpectationConvergence
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ENNReal BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueDoubledRegularized_compact_expectation_tendsto {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun k => ∫ x, f x ∂bakryEmeryNormalizedGibbs volume
      (gueDoubledRegularizedPotential n (gueRegularizationScale k))) atTop
      (nhds (∫ x, f x ∂gueDoubledOrderedMeasure n)) := by
  obtain ⟨C, hC⟩ := hf.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hb (x) : ‖f x‖≤C := hC (mem_range_self x)
  rw [gueDoubledOrderedMeasure_integral]
  exact gueDoubledRegularized_expectation_tendsto hn f hf C
    ((norm_nonneg (f 0)).trans (hb 0)) hb

theorem gueDoubledRegularized_entropy_tendsto {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : Continuous f) (hc : HasCompactSupport f) :
    Tendsto (fun k => squareEntropy (bakryEmeryNormalizedGibbs volume
      (gueDoubledRegularizedPotential n (gueRegularizationScale k))) f) atTop
      (nhds (squareEntropy (gueDoubledOrderedMeasure n) f)) := by
  have hs := gueDoubledRegularized_compact_expectation_tendsto hn (fun x => f x^2)
    (hf.pow 2) (by
      apply hc.mono
      intro x hx hz
      apply hx
      simp [hz])
  have hl := gueDoubledRegularized_compact_expectation_tendsto hn
    (fun x => f x^2*Real.log (f x^2)) (continuous_square_mul_log hf)
    (compactSupport_square_mul_log hc)
  unfold squareEntropy
  exact hl.sub (Real.continuous_mul_log.continuousAt.tendsto.comp hs)

/-- Sharp-curvature log-Sobolev bound for the actual ordered GUE density,
with independent auxiliary Gaussian coordinates. -/
theorem gueDoubledOrderedMeasure_square_lsi {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (gueDoubledOrderedMeasure n) f ≤
      (2/(n : ℝ))*∫ x, ‖gradient f x‖^2 ∂gueDoubledOrderedMeasure n := by
  have he := gueDoubledRegularized_entropy_tendsto hn f hf.continuous hs
  have hg : Continuous (gradient f) :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n×Fin 2))).symm.continuous.comp
      (hf.fderiv_right (m := 0) (by norm_num)).continuous
  have hgs : HasCompactSupport (fun x => ‖gradient f x‖^2) :=
    ((hs.fderiv ℝ).comp_left
      (g := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n×Fin 2))).symm) (map_zero _)).comp_left
      (g := fun x : EuclideanSpace ℝ (Fin n×Fin 2) => ‖x‖^2) (by simp)
  have hi := gueDoubledRegularized_compact_expectation_tendsto hn
    (fun x => ‖gradient f x‖^2) (hg.norm.pow 2) hgs
  exact le_of_tendsto_of_tendsto he (tendsto_const_nhds.mul hi)
    (Eventually.of_forall (fun k => gueDoubledRegularizedGibbs_lsi hn
      (gueRegularizationScale_pos k) f hf hs))

#print axioms gueDoubledOrderedMeasure_square_lsi
#print axioms gueDoubledRegularized_entropy_tendsto
end
end GinibrePoincare
