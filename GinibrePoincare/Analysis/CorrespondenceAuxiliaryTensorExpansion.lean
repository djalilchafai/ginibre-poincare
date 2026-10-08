module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryHermiteRectangleL2
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section
open MeasureTheory
open scoped BigOperators ComplexConjugate
namespace GinibrePoincare
noncomputable section
open ComplexHermite

def tensorHermiteScale (n : ℕ) (p q : Fin n → ℕ) : ℝ :=
  ∏ j, oneDimNormalization n (p j) * oneDimNormalization n (q j)

theorem tensorHermiteScale_pos (n : ℕ) (hn : 0 < n) (p q : Fin n → ℕ) :
    0 < tensorHermiteScale n p q := by
  unfold tensorHermiteScale oneDimNormalization
  apply Finset.prod_pos
  intro j hj
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  positivity

abbrev TensorHermiteContraction {n : ℕ} (p q : Fin n → ℕ) :=
  ∀ j, Fin (min (p j) (q j)+1)

def tensorHermiteScalar {n : ℕ} (p q : Fin n → ℕ)
    (k : TensorHermiteContraction p q) : ℂ :=
  ∏ j, (-((n : ℝ)⁻¹ : ℂ))^(k j).val * ((k j).val.factorial : ℂ) *
    (Nat.choose (p j) (k j).val : ℂ) * (Nat.choose (q j) (k j).val : ℂ)

theorem multivariateNormalized_tensor_expansion (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) (z : Configuration n) :
    multivariateNormalized n hn p q z = (tensorHermiteScale n p q : ℂ) *
      ∑ k : TensorHermiteContraction p q, tensorHermiteScalar p q k *
        ∏ j, z j^(p j-(k j).val) * conj (z j)^(q j-(k j).val) := by
  classical
  simp only [multivariateNormalized,normalizedEval_eq_sum]
  rw [Finset.prod_mul_distrib]
  have hsum (j : Fin n) :
      (∑ k ∈ Finset.range (min (p j) (q j)+1),
        (-((n : ℝ)⁻¹ : ℂ))^k * (k.factorial : ℂ) * (Nat.choose (p j) k : ℂ) *
          (Nat.choose (q j) k : ℂ) * z j^(p j-k) * conj (z j)^(q j-k)) =
      ∑ k : Fin (min (p j) (q j)+1),
        (-((n : ℝ)⁻¹ : ℂ))^k.val * (k.val.factorial : ℂ) *
          (Nat.choose (p j) k.val : ℂ) * (Nat.choose (q j) k.val : ℂ) *
          (z j^(p j-k.val) * conj (z j)^(q j-k.val)) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  simp_rw [hsum]
  rw [Fintype.prod_sum]
  congr 1
  · simp [tensorHermiteScale]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.prod_mul_distrib]
    rfl

theorem multivariateNormalizedL2_tensor_expansion (n : ℕ) (hn : 0 < n)
    (p q : Fin n → ℕ) :
    multivariateNormalizedL2 n hn p q = (tensorHermiteScale n p q : ℂ) •
      ∑ k : TensorHermiteContraction p q, tensorHermiteScalar p q k •
        multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
          (fun j => q j-(k j).val) := by
  classical
  apply Lp.ext
  have hall : ∀ᵐ z ∂complexGaussianMeasure n, ∀ k : TensorHermiteContraction p q,
      (tensorHermiteScalar p q k • multivariateMixedMonomialL2 n hn
        (fun j => p j-(k j).val) (fun j => q j-(k j).val)) z =
      tensorHermiteScalar p q k * ∏ j, z j^(p j-(k j).val) *
        conj (z j)^(q j-(k j).val) := by
    rw [ae_all_iff]
    intro k
    filter_upwards [Lp.coeFn_smul (tensorHermiteScalar p q k)
      (multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
        (fun j => q j-(k j).val)),
      (memLp_two_multivariateMixedMonomial n hn (fun j => p j-(k j).val)
        (fun j => q j-(k j).val)).coeFn_toLp] with z h1 h2
    rw [h1]
    simp only [Pi.smul_apply,smul_eq_mul]
    change tensorHermiteScalar p q k * (memLp_two_multivariateMixedMonomial n hn
      (fun j => p j-(k j).val) (fun j => q j-(k j).val)).toLp _ z = _
    rw [h2]
  filter_upwards [multivariateNormalizedL2_coeFn n hn p q,
    Lp.coeFn_smul (tensorHermiteScale n p q : ℂ)
      (∑ k : TensorHermiteContraction p q, tensorHermiteScalar p q k •
        multivariateMixedMonomialL2 n hn (fun j => p j-(k j).val)
          (fun j => q j-(k j).val)),
    Lp.coeFn_fun_finsetSum Finset.univ (fun k : TensorHermiteContraction p q =>
      tensorHermiteScalar p q k • multivariateMixedMonomialL2 n hn
        (fun j => p j-(k j).val) (fun j => q j-(k j).val)),hall]
    with z hF hs hsum hall
  rw [hF,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hsum]
  simp_rw [hall]
  exact multivariateNormalized_tensor_expansion n hn p q z

#print axioms tensorHermiteScale_pos
#print axioms multivariateNormalized_tensor_expansion
#print axioms multivariateNormalizedL2_tensor_expansion
end
end GinibrePoincare
