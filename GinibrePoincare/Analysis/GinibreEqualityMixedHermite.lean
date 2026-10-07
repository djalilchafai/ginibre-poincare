module

public import GinibrePoincare.Analysis.GinibreEqualityMixedFactor

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MvPolynomial ComplexHermite
open scoped BigOperators ComplexConjugate
set_option maxHeartbeats 600000

def ginibreMixedHermitePolynomial (n : ℕ) (hn : 0<n) (p q : Fin n → ℕ) : GinibreMixedPolynomial n :=
  ∏ j : Fin n, MvPolynomial.rename (fun k : Fin 2 => (j,k)) (normalized n hn (p j) (q j))

theorem ginibreMixedHermitePolynomial_eval (n : ℕ) (hn : 0<n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    ginibreMixedPolynomialEval (ginibreMixedHermitePolynomial n hn p q) z =
      multivariateNormalized n hn p q z := by
  unfold ginibreMixedPolynomialEval ginibreMixedHermitePolynomial multivariateNormalized
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [MvPolynomial.eval_rename]
  unfold normalizedEval
  have hv : ((fun k : Fin n × Fin 2 => if k.2=0 then z k.1 else conj (z k.1)) ∘
      fun k : Fin 2 => (j,k)) = ![z j,conj (z j)] := by
    funext k
    fin_cases k <;> simp
  rw [hv]

private theorem ginibreMixedHermiteCoordinate_specialize_degree (n : ℕ) (hn : 0<n)
    (p q : ℕ) (j : Fin n) (z : Configuration n) :
    (ginibreMixedPolynomialSpecialize z
      (MvPolynomial.rename (fun k : Fin 2 => (j,k)) (normalized n hn p q))).totalDegree ≤ q := by
  classical
  unfold ginibreMixedPolynomialSpecialize
  rw [MvPolynomial.aeval_rename]
  unfold normalized raw
  rw [map_mul,map_sum]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,MvPolynomial.totalDegree_C,zero_add]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k hk
  simp only [map_mul,map_pow,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,Z,W,
    MvPolynomial.aeval_X,Function.comp_apply]
  simp only [if_true,show (1:Fin 2)≠0 by decide,if_false]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [←map_pow,←map_mul,MvPolynomial.totalDegree_C,totalDegree_X_pow,zero_add]
  exact Nat.sub_le q k

/-- The formal mixed Hermite tensor has antiholomorphic degree at most its
actual antiholomorphic multi-index degree after every holomorphic specialization. -/
theorem ginibreMixedHermitePolynomial_specialize_degree (n : ℕ) (hn : 0<n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    (ginibreMixedPolynomialSpecialize z (ginibreMixedHermitePolynomial n hn p q)).totalDegree ≤
      ∑ j : Fin n,q j := by
  unfold ginibreMixedHermitePolynomial
  rw [map_prod]
  exact (MvPolynomial.totalDegree_finsetProd _ _).trans
    (Finset.sum_le_sum (fun j _ => ginibreMixedHermiteCoordinate_specialize_degree n hn (p j) (q j) j z))

def ginibreMixedFiniteHermitePolynomial (n : ℕ) (hn : 0<n)
    (c : HermiteMultiIndex n →₀ ℂ) : GinibreMixedPolynomial n :=
  c.sum (fun pq a => C a * ginibreMixedHermitePolynomial n hn pq.1 pq.2)

theorem ginibreMixedFiniteHermitePolynomial_eval (n : ℕ) (hn : 0<n)
    (c : HermiteMultiIndex n →₀ ℂ) (z : Configuration n) :
    ginibreMixedPolynomialEval (ginibreMixedFiniteHermitePolynomial n hn c) z =
      finiteHermiteFunction n hn c z := by
  classical
  simp only [ginibreMixedPolynomialEval,ginibreMixedFiniteHermitePolynomial,Finsupp.sum,
    map_sum,map_mul,MvPolynomial.eval_C]
  unfold finiteHermiteFunction
  simp only [Finsupp.linearCombination_apply,Finsupp.sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro pq hpq
  rw [←ginibreMixedPolynomialEval,ginibreMixedHermitePolynomial_eval]

/-- An actual finite Hermite combination with antiholomorphic degrees ≤K
has a formal mixed polynomial representative with the same specialization bound. -/
theorem ginibreMixedFiniteHermitePolynomial_specialize_degree (n : ℕ) (hn : 0<n)
    (c : HermiteMultiIndex n →₀ ℂ) (K : ℕ)
    (hc : ∀ pq ∈ c.support,totalAntiDegree pq ≤ K) (z : Configuration n) :
    (ginibreMixedPolynomialSpecialize z (ginibreMixedFiniteHermitePolynomial n hn c)).totalDegree ≤ K := by
  classical
  unfold ginibreMixedFiniteHermitePolynomial Finsupp.sum
  rw [map_sum]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro pq hpq
  rw [map_mul]
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  simp only [ginibreMixedPolynomialSpecialize,MvPolynomial.aeval_C,MvPolynomial.algebraMap_eq,
    MvPolynomial.totalDegree_C,zero_add]
  exact (ginibreMixedHermitePolynomial_specialize_degree n hn pq.1 pq.2 z).trans (hc pq hpq)

end GinibrePoincare
