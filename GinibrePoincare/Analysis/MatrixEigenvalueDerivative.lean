module

public import GinibrePoincare.Analysis.MatrixOverlap
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add

@[expose] public section

/-! # First-order perturbation of a differentiable eigenpair

Differentiating the eigenvector equation and pairing with a normalized left
eigenvector cancels the derivative of the right eigenvector. The theorem does
not assume the claimed eigenvalue derivative formula. Existence of local
differentiable eigenpairs at simple spectrum is a separate result.
-/

open scoped BigOperators Topology
open Matrix Filter

namespace GinibrePoincare
noncomputable section
variable {n : Type*} [Fintype n]

/-- Actual first-order eigenvalue perturbation along an arbitrary real path. -/
theorem matrixEigenvalue_derivative
    (A : ℝ → Matrix n n ℂ) (r : ℝ → n → ℂ) (eig : ℝ → ℂ)
    (t : ℝ) (A' : Matrix n n ℂ) (r' : n → ℂ) (eig' : ℂ) (l : n → ℂ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hr : ∀ i, HasDerivAt (fun s => r s i) (r' i) t)
    (heig : HasDerivAt eig eig' t)
    (heigen : ∀ᶠ s in 𝓝 t, A s *ᵥ r s = eig s • r s)
    (hleft : star l ᵥ* A t = eig t • star l)
    (hnorm : star l ⬝ᵥ r t = 1) :
    eig' = star l ⬝ᵥ (A' *ᵥ r t) := by
  have hd (i : n) :
      (A' *ᵥ r t) i + (A t *ᵥ r') i = eig' * r t i + eig t * r' i := by
    have hsum := HasDerivAt.fun_sum (u := Finset.univ)
      (fun j _ => (hA i j).mul (hr j))
    have hprod := heig.mul (hr i)
    have heq : (fun s => eig s * r s i) =ᶠ[𝓝 t]
        (fun s => ∑ j, A s i j * r s j) := by
      filter_upwards [heigen] with s hs
      simpa [Matrix.mulVec, dotProduct] using (congr_fun hs i).symm
    have hder := (hsum.congr_of_eventuallyEq heq).unique hprod
    simpa only [Finset.sum_add_distrib, Matrix.mulVec, dotProduct] using hder
  have hpaired :
      star l ⬝ᵥ (A' *ᵥ r t) + star l ⬝ᵥ (A t *ᵥ r') =
        eig' * (star l ⬝ᵥ r t) + eig t * (star l ⬝ᵥ r') := by
    simp only [dotProduct, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have hi := congrArg (fun z : ℂ => star (l i) * z) (hd i)
    simp only [Pi.star_apply]
    linear_combination hi
  rw [Matrix.dotProduct_mulVec (star l) (A t) r', hleft] at hpaired
  simp only [smul_dotProduct, smul_eq_mul, hnorm, mul_one] at hpaired
  exact (add_right_cancel hpaired).symm

/-- The same derivative in the paper's trace notation. -/
theorem matrixEigenvalue_derivative_trace
    (A : ℝ → Matrix n n ℂ) (r : ℝ → n → ℂ) (eig : ℝ → ℂ)
    (t : ℝ) (A' : Matrix n n ℂ) (r' : n → ℂ) (eig' : ℂ) (l : n → ℂ)
    (hA : ∀ i j, HasDerivAt (fun s => A s i j) (A' i j) t)
    (hr : ∀ i, HasDerivAt (fun s => r s i) (r' i) t)
    (heig : HasDerivAt eig eig' t)
    (heigen : ∀ᶠ s in 𝓝 t, A s *ᵥ r s = eig s • r s)
    (hleft : star l ᵥ* A t = eig t • star l)
    (hnorm : star l ⬝ᵥ r t = 1) :
    eig' = Matrix.trace (matrixRankOneProjector (r t) l * A') := by
  rw [matrixRankOneProjector_trace_mul]
  exact matrixEigenvalue_derivative A r eig t A' r' eig' l hA hr heig heigen hleft hnorm

#print axioms matrixEigenvalue_derivative
#print axioms matrixEigenvalue_derivative_trace

end
end GinibrePoincare
