module

public import GinibrePoincare.Analysis.GinibreDrivenPathLocalUniqueness
public import GinibrePoincare.Analysis.GinibreDrivenPathFactorization

@[expose] public section

/-! # Actual local uniqueness of the original additive-noise integral equation -/
open Set Metric Filter MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem ginibreDrivenPath_local_pathwise_unique (n : ℕ) (α : ℝ)
    (N X Z : ℝ → Configuration n) (hN : Continuous N) (hX : Continuous X) (hZ : Continuous Z)
    (hXN : IsGinibreDrivenPath n α N X) (hZN : IsGinibreDrivenPath n α N Z)
    (h0 : X 0 = Z 0) (hz : CollisionFree (X 0)) :
    ∃ T > (0 : ℝ), EqOn X Z (Icc 0 T) := by
  obtain ⟨K, s, hs, hb⟩ := ginibreLangevinDrift_local_lipschitz n α (X 0) hz
  obtain ⟨g, hg, heq⟩ := hb.extend_finite_dimension
  have hsX : ∀ᶠ t in nhds 0, X t ∈ s := hX.continuousAt.eventually hs
  have hsZ : ∀ᶠ t in nhds 0, Z t ∈ s := hZ.continuousAt.eventually (by rw [← h0]; exact hs)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp (hsX.and hsZ)
  let T := δ/2
  have hT : 0 < T := by dsimp [T]; linarith
  have hsub (t : ℝ) (ht : t ∈ Icc 0 T) : X t ∈ s ∧ Z t ∈ s := by
    apply hδs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    dsimp [T] at ht
    linarith [ht.2]
  have heX (t : ℝ) (ht : t ∈ Icc 0 T) : X t-N t = X 0+∫ u in (0 : ℝ)..t, g (X u) := by
    have h := hXN.2 t ht.1
    have hi : (∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u)) = ∫ u in (0 : ℝ)..t, g (X u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact heq (hsub u (by rw [uIcc_of_le ht.1] at hu; exact ⟨hu.1, hu.2.trans ht.2⟩)).1
    rw [hi] at h
    rw [h]
    abel
  have heZ (t : ℝ) (ht : t ∈ Icc 0 T) : Z t-N t = Z 0+∫ u in (0 : ℝ)..t, g (Z u) := by
    have h := hZN.2 t ht.1
    have hi : (∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (Z u)) = ∫ u in (0 : ℝ)..t, g (Z u) := by
      apply intervalIntegral.integral_congr
      intro u hu
      exact heq (hsub u (by rw [uIcc_of_le ht.1] at hu; exact ⟨hu.1, hu.2.trans ht.2⟩)).2
    rw [hi] at h
    rw [h]
    abel
  have hDeriv (W : ℝ → Configuration n) (hW : Continuous W)
      (heW : ∀ t ∈ Icc 0 T, W t-N t = W 0+∫ u in (0 : ℝ)..t, g (W u))
      (t : ℝ) (ht : t ∈ Ico 0 T) :
      HasDerivWithinAt (fun u => W u-N u) (g (W t)) (Ici t) t := by
    have hd := (((hg.continuous.comp hW).integral_hasStrictDerivAt 0 t).hasDerivAt.const_add (W 0)).hasDerivWithinAt (s := Ici t)
    apply hd.congr_of_eventuallyEq
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with u hu htu
      exact heW u ⟨ht.1.trans hu, htu.le⟩
    · exact heW t ⟨ht.1, ht.2.le⟩
  have hv (t : ℝ) : LipschitzWith (lipschitzExtensionConstant (Configuration n)*K)
      (fun y => g (y+N t)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_add_right] using hg.dist_le_mul (x+N t) (y+N t)
  have hu := ODE_solution_unique hv (hX.sub hN).continuousOn
    (fun t ht => by
      convert! hDeriv X hX heX t ht using 1 <;> simp only [Pi.sub_apply, sub_add_cancel])
    (hZ.sub hN).continuousOn
    (fun t ht => by
      convert! hDeriv Z hZ heZ t ht using 1 <;> simp only [Pi.sub_apply, sub_add_cancel])
    (show X 0-N 0 = Z 0-N 0 from congrArg (fun x => x-N 0) h0)
  refine ⟨T, hT, ?_⟩
  intro t ht
  simpa only [Pi.sub_apply, sub_left_inj] using hu ht

end
end GinibrePoincare
