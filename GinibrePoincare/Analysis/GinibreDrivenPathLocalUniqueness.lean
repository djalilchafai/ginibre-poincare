module

public import GinibrePoincare.Analysis.GinibreDrivenPathLocalExistence

@[expose] public section

/-! # Local pathwise uniqueness of the actual continuous-noise correction -/
open Set Metric Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenPath_continuous_noise_correction_unique (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) (Y Z : ℝ → Configuration n)
    (hY0 : Y 0 = z) (hZ0 : Z 0 = z)
    (hY : ∀ᶠ t in nhds 0, HasDerivAt Y (ginibreLangevinDrift n α (Y t+N t)) t)
    (hZ : ∀ᶠ t in nhds 0, HasDerivAt Z (ginibreLangevinDrift n α (Z t+N t)) t) :
    Y =ᶠ[nhds 0] Z := by
  obtain ⟨K, s, hs, hb⟩ := ginibreLangevinDrift_local_lipschitz n α z hz
  have hYc : ContinuousAt (fun t => Y t+N t) 0 := hY.self_of_nhds.continuousAt.add hN.continuousAt
  have hZc : ContinuousAt (fun t => Z t+N t) 0 := hZ.self_of_nhds.continuousAt.add hN.continuousAt
  have hYs : ∀ᶠ t in nhds 0, Y t+N t ∈ s := hYc.eventually (by
    dsimp only
    rw [hY0, hN0, add_zero]
    change s ∈ nhds z
    exact hs)
  have hZs : ∀ᶠ t in nhds 0, Z t+N t ∈ s := hZc.eventually (by
    dsimp only
    rw [hZ0, hN0, add_zero]
    change s ∈ nhds z
    exact hs)
  apply ODE_solution_unique_of_eventually (K := K)
    (v := fun t y => ginibreLangevinDrift n α (y+N t))
    (s := fun t => {y | y+N t ∈ s})
  · apply Filter.Eventually.of_forall
    intro t
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simpa only [dist_add_right] using hb.dist_le_mul (x+N t) hx (y+N t) hy
  · exact hY.and hYs
  · exact hZ.and hZs
  · rw [hY0, hZ0]

end
end GinibrePoincare
