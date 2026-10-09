module

public import GinibrePoincare.Analysis.GinibreStochasticRadialDirection
public import GinibrePoincare.Analysis.GinibreStochasticCIRGenerator

@[expose] public section

/-! # Positivity and continuity of the relative radius

The global original solution is adapted, continuous and collision-free almost
surely. Composing it with the smooth polynomial `pairwiseRadius` gives
adaptation and continuity. For `2 ≤ n`, collision-freeness implies that this
radius is strictly positive; the initial value follows from the initial
condition of the original solution. All path properties hold on one event of
full measure for every time, rather than separately almost surely at each time. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreBrownianMaximalProcess_radius_path_properties
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun t ω => pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
    ∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      (∀ t, 0 < pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      pairwiseRadius (ginibreBrownianMaximalProcess n α z B 0 ω)=pairwiseRadius z := by
  obtain ⟨hAdapt, hPath⟩ := ginibreBrownianMaximalProcess_global_original_solution
    (by omega) α z hz B P hB hind
  have hr := (ginibre_contDiff_pairwiseRadius n).continuous
  refine ⟨fun t => (hr.measurable.comp (hAdapt t).measurable).stronglyMeasurable,?_⟩
  filter_upwards [hPath] with ω hω
  have hX : Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B t ω) := by
    simpa only [Real.toNNReal_coe] using
      (show Continuous (fun t : ℝ≥0 => ginibreBrownianMaximalProcess n α z B (t : ℝ).toNNReal ω)
        from hω.1.comp NNReal.continuous_coe)
  refine ⟨hr.comp hX,?_,?_⟩
  · intro t
    apply pairwiseRadius_pos_of_collisionFree hn
    simpa only [Real.toNNReal_coe] using hω.2.2.1 t t.coe_nonneg
  · rw [hω.2.1]
end
end GinibrePoincare
