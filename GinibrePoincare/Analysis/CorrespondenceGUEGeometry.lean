module
public import GinibrePoincare.Analysis.CorrespondenceGUEConvexity
public import GinibrePoincare.Analysis.GinibreCollisionCutoff
@[expose] public section
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set

def gueComplexEmbedding (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) : Configuration n :=
  fun i => (x i : ℂ)

theorem gue_pairs_eq_vandermonde (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    (∏ p ∈ guePairs n, (x p.2-x p.1)^2) = vandermondeWeight (gueComplexEmbedding n x) := by
  unfold guePairs vandermondeWeight
  rw [vandermonde_eq_product]
  simp only [map_prod, gueComplexEmbedding,← Complex.ofReal_sub, Complex.normSq_ofReal]
  rw [Finset.prod_filter]
  have hp := Finset.prod_product (Finset.univ : Finset (Fin n)) Finset.univ
    (fun p : Fin n × Fin n => if p.1<p.2 then (x p.2-x p.1)^2 else 1)
  simp only [Finset.univ_product_univ] at hp
  rw [hp]
  apply Finset.prod_congr rfl
  intro i hi
  have hI : Finset.Ioi i = Finset.univ.filter (fun j : Fin n => i<j) := by
    ext j
    simp
  rw [hI, Finset.prod_filter]
  simp only [pow_two]

/-- The real GUE density is symmetric, by the genuine Vandermonde sign law. -/
theorem gueRawDensity_symmetric (n : ℕ) (σ : Fin n ≃ Fin n)
    (x : EuclideanSpace ℝ (Fin n)) :
    gueRawDensity n (WithLp.toLp 2 (fun i => x (σ i))) = gueRawDensity n x := by
  unfold gueRawDensity
  rw [gue_pairs_eq_vandermonde, gue_pairs_eq_vandermonde]
  have hs : ∑ i, (WithLp.toLp 2 (fun i => x (σ i)) i)^2 = ∑ i, (x i)^2 := by
    simpa only [PiLp.toLp_apply] using Equiv.sum_comp σ (fun i => (x i)^2)
  rw [hs]
  congr 1
  exact vandermondeWeight_symmetric n σ (gueComplexEmbedding n x)

/-- Collisions lie in the exact zero set of the real GUE density. -/
theorem gueRawDensity_zero_iff_collision (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gueRawDensity n x=0 ↔ ∃ i j : Fin n, i≠j ∧ x i=x j := by
  unfold gueRawDensity
  rw [gue_pairs_eq_vandermonde, mul_eq_zero]
  simp only [Real.exp_ne_zero, false_or]
  unfold vandermondeWeight
  rw [Complex.normSq_eq_zero, vandermonde_eq_zero_iff, mem_collisionSet_iff]
  simp [gueComplexEmbedding, and_comm]

#print axioms gue_pairs_eq_vandermonde
#print axioms gueRawDensity_symmetric
#print axioms gueRawDensity_zero_iff_collision
end
end GinibrePoincare
