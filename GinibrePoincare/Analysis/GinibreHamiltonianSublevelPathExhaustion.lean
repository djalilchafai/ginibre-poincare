module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceSublevelStopped
public import GinibrePoincare.Analysis.GinibreHamiltonianCompactPathWeight

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Every continuous collision-free path on a compact horizon survives some
Hamiltonian sublevel. The bound is derived from the actual path. -/
theorem ginibreHamiltonian_compact_path_sublevel_exhaustion
    {n : ℕ} (T : ℝ) (x : C(Icc (0 : ℝ) T, Configuration n))
    (hCF : ∀ t, CollisionFree (x t)) :
    ∃ R : ℝ, ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R := by
  have hH : Continuous (fun t => ginibreHamiltonian n (x t)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (ginibreHamiltonian_contDiffAt n (x t) (hCF t)).continuousAt.comp x.continuous.continuousAt
  have hK := isCompact_range hH
  obtain ⟨R, hR, hBound⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨R+1, fun t => ?_⟩
  change Real.exp (-(R+1)) < ginibreWeight n (x t)
  rw [← ginibreHamiltonian_exp_neg (x t) (hCF t)]
  apply Real.exp_lt_exp.mpr
  have hb := hBound (ginibreHamiltonian n (x t)) (mem_range_self t)
  have hh := le_trans (le_abs_self (ginibreHamiltonian n (x t))) hb
  linarith

/-- Hamiltonian survival depends only on the range of the path and is
unchanged by compact-horizon time reversal. -/
theorem ginibreHamiltonian_compact_sublevel_survival_reverse
    {n : ℕ} (T : ℝ) (hT : 0 ≤ T) (R : ℝ)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    (∀ t, (x.comp (ginibreHamiltonianCompactReverseTime T hT)) t ∈
      ginibreHamiltonianOUSublevelDomain n R) ↔
    (∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R) := by
  constructor
  · intro h t
    have hh := h ((ginibreHamiltonianCompactReverseTime T hT) t)
    have he : (ginibreHamiltonianCompactReverseTime T hT)
        ((ginibreHamiltonianCompactReverseTime T hT) t) = t := by
      apply Subtype.ext
      change T - (T - t.val) = t.val
      ring
    simpa only [ContinuousMap.comp_apply, he] using hh
  · intro h t
    exact h ((ginibreHamiltonianCompactReverseTime T hT) t)

theorem ginibreHamiltonian_compact_path_natural_sublevel_exhaustion
    {n : ℕ} (T : ℝ) (x : C(Icc (0 : ℝ) T, Configuration n))
    (hCF : ∀ t, CollisionFree (x t)) :
    ∃ k : ℕ, ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n (k : ℝ) := by
  obtain ⟨R, hR⟩ := ginibreHamiltonian_compact_path_sublevel_exhaustion T x hCF
  obtain ⟨k, hk⟩ := exists_nat_gt R
  refine ⟨k, fun t => ?_⟩
  have hh := hR t
  change Real.exp (-R) < ginibreWeight n (x t) at hh
  change Real.exp (-(k : ℝ)) < ginibreWeight n (x t)
  exact lt_trans (Real.exp_lt_exp.mpr (neg_lt_neg hk)) hh

theorem ginibreHamiltonian_compact_path_survival_exhaustion_iff
    {n : ℕ} (T : ℝ) (x : C(Icc (0 : ℝ) T, Configuration n)) :
    (∃ k : ℕ, ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n (k : ℝ)) ↔
      (∀ t, CollisionFree (x t)) := by
  constructor
  · rintro ⟨k, hk⟩ t
    have hh := hk t
    have hMem : x t ∈ ginibreHamiltonianSublevel n k := by
      rw [ginibreHamiltonianSublevel_eq_weight_superlevel]
      exact (show Real.exp (-(k : ℝ)) < ginibreWeight n (x t) from hh).le
    exact hMem.1
  · exact ginibreHamiltonian_compact_path_natural_sublevel_exhaustion T x

#print axioms ginibreHamiltonian_compact_path_survival_exhaustion_iff
#print axioms ginibreHamiltonian_compact_path_sublevel_exhaustion
#print axioms ginibreHamiltonian_compact_sublevel_survival_reverse
end
end GinibrePoincare
