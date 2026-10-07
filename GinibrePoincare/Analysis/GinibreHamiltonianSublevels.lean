module

public import GinibrePoincare.Analysis.GinibreHamiltonianCoercivity

@[expose] public section

/-! Actual Hamiltonian sublevels are compact subsets of the collision-free domain. -/
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def ginibreHamiltonianSublevel (n : ℕ) (B : ℝ) : Set (Configuration n) :=
  {z | CollisionFree z ∧ ginibreHamiltonian n z ≤ B}

theorem ginibreHamiltonianSublevel_eq_weight_superlevel (n : ℕ) (B : ℝ) :
    ginibreHamiltonianSublevel n B = {z | Real.exp (-B) ≤ ginibreWeight n z} := by
  ext z
  constructor
  · intro hz
    change Real.exp (-B) ≤ ginibreWeight n z
    rw [← ginibreHamiltonian_exp_neg z hz.1]
    exact Real.exp_le_exp.mpr (neg_le_neg hz.2)
  · intro hz
    change Real.exp (-B) ≤ ginibreWeight n z at hz
    have hw : 0 < ginibreWeight n z := lt_of_lt_of_le (Real.exp_pos _) hz
    have hc : CollisionFree z := (collisionFree_iff_not_mem_collisionSet z).mpr
      (fun h => (ne_of_gt hw) ((ginibreWeight_eq_zero_iff n z).mpr h))
    refine ⟨hc, ?_⟩
    rw [← ginibreHamiltonian_exp_neg z hc] at hz
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp hz)

theorem ginibreHamiltonianSublevel_isClosed (n : ℕ) (B : ℝ) :
    IsClosed (ginibreHamiltonianSublevel n B) := by
  rw [ginibreHamiltonianSublevel_eq_weight_superlevel]
  have hg : Continuous (gaussianWeight n : Configuration n → ℝ) := by
    unfold gaussianWeight
    exact (((contDiff_const : ContDiff ℝ ∞ (fun _ : Configuration n => -(n : ℝ))).mul
      contDiff_configurationNormSq).exp).continuous
  exact isClosed_le continuous_const (hg.mul (contDiff_vandermondeWeight n).continuous)

theorem ginibreHamiltonianSublevel_isCompact {n : ℕ} (hn : 0 < n) (B : ℝ) :
    IsCompact (ginibreHamiltonianSublevel n B) := by
  let A : ℝ := (B+ginibreHamiltonianLowerBoundConstant n)/((n : ℝ)/2)
  apply (isCompact_closedBall (0 : Configuration n) (|A|+1)).of_isClosed_subset
    (ginibreHamiltonianSublevel_isClosed n B)
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ |A|+1)).mpr
  intro i
  have hN : 0 < (n : ℝ)/2 := by exact div_pos (by exact_mod_cast hn) (by norm_num)
  have hq : configurationNormSq z ≤ A := by
    apply (le_div_iff₀ hN).mpr
    have h := ginibreHamiltonian_quadratic_lower_bound hn z hz.1
    have hB := hz.2
    nlinarith
  have hi : Complex.normSq (z i) ≤ configurationNormSq z :=
    Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  rw [Complex.normSq_eq_norm_sq] at hi
  have hA := le_abs_self A
  have hp := abs_nonneg A
  have hz0 := norm_nonneg (z i)
  nlinarith [sq_nonneg (|A|)]

end
end GinibrePoincare
