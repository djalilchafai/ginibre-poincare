module

public import GinibrePoincare.Analysis.GinibreHamiltonian

@[expose] public section

/-! Genuine divergence of the Hamiltonian along collision-free paths to a collision. -/
open scoped Topology
open Filter
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonian_tendsto_collision {n : ℕ} {ι : Type*}
    {l : Filter ι} {Z : ι → Configuration n} {z : Configuration n}
    (hZ : Tendsto Z l (𝓝 z)) (hz : z ∈ collisionSet n)
    (hfree : ∀ᶠ t in l, CollisionFree (Z t)) :
    Tendsto (fun t => ginibreHamiltonian n (Z t)) l atTop := by
  have hv : Tendsto (fun t => vandermondeWeight (Z t)) l (𝓝 (0 : ℝ)) := by
    have h : Tendsto (vandermondeWeight : Configuration n → ℝ) (𝓝 z)
        (𝓝 (vandermondeWeight z)) := (contDiff_vandermondeWeight n).continuous.continuousAt
    rw [(vandermondeWeight_eq_zero_iff z).mpr hz] at h
    exact h.comp hZ
  have hp : ∀ᶠ t in l, vandermondeWeight (Z t) ∈ Set.Ioi (0 : ℝ) :=
    hfree.mono (fun t ht => vandermondeWeight_pos_of_collisionFree (Z t) ht)
  have hl : Tendsto (fun t => Real.log (vandermondeWeight (Z t))) l atBot :=
    Real.tendsto_log_nhdsGT_zero.comp (tendsto_nhdsWithin_iff.mpr ⟨hv, hp⟩)
  have hr : Tendsto (fun t => (n : ℝ) * configurationNormSq (Z t)) l
      (𝓝 ((n : ℝ) * configurationNormSq z)) :=
    tendsto_const_nhds.mul
      ((contDiff_configurationNormSq (n := n)).continuous.continuousAt.tendsto.comp hZ)
  convert hr.add_atTop (tendsto_neg_atBot_atTop.comp hl) using 1
  funext t
  exact sub_eq_add_neg _ _

end
end GinibrePoincare
