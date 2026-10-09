module

public import GinibrePoincare.Analysis.FiniteDimensionalItoIntervalRefinement
public import GinibrePoincare.Analysis.GinibreBrownianIntegralPartialGeometry

@[expose] public section

open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Literal two-grid intersection identity between a fixed-horizon partial
Brownian sum and the actual horizon-t left sum. -/
theorem brownianUniformPartialSum_difference_horizon_refinement {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (F G : ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t ≤ T)
    (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (ω : Ω) :
    brownianUniformPartialSum B F T N t ω - brownianUniformLeftSum B G t M ω =
      ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range M,
        (F (itoUniformNNTime T N i) ω-G (itoUniformNNTime t M j) ω)*
        (B (max (max (min t (itoUniformNNTime T N i)) (itoUniformNNTime t M j))
          (min (min t (itoUniformNNTime T N (i+1))) (itoUniformNNTime t M (j+1)))) ω -
          B (max (min t (itoUniformNNTime T N i)) (itoUniformNNTime t M j)) ω) := by
  rw [brownianUniformPartialSum_eq_stopped_leftsum]
  unfold brownianUniformLeftSum
  exact itoWeightedIntervalSums_difference_intersections (fun s => B s ω) t
    (fun i => min t (itoUniformNNTime T N i)) (itoUniformNNTime t M) N M
    (monotone_const.min (itoUniformNNTime_mono T N)) (itoUniformNNTime_mono t M)
    (by simp [itoUniformNNTime, itoUniformTime])
    (by rw [itoUniformNNTime_end T N hN, min_eq_left ht])
    (by simp [itoUniformNNTime, itoUniformTime]) (itoUniformNNTime_end t M hM)
    (fun i => F (itoUniformNNTime T N i) ω) (fun j => G (itoUniformNNTime t M j) ω)

end
end GinibrePoincare
