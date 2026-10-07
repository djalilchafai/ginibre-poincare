module

public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Calculus.FDeriv.Pow
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Tactic

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

section
variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype ι] [DecidableEq ι]

/-- Evaluation of a multivariate polynomial on a family of complex observables. -/
def observablePolynomial (φ : ι → E → ℂ) (Q : MvPolynomial ι ℂ) (z : E) : ℂ :=
  MvPolynomial.eval (fun i => φ i z) Q

/-- Smoothness is preserved by polynomial evaluation. -/
theorem differentiable_observablePolynomial (φ : ι → E → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (Q : MvPolynomial ι ℂ) :
    Differentiable ℝ (observablePolynomial φ Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
      have heq : observablePolynomial φ (MvPolynomial.C c) = fun _ => c := by
        funext z; simp [observablePolynomial]
      rw [heq]; exact differentiable_const c
  | add P Q hP hQ =>
      have heq : observablePolynomial φ (P + Q) = observablePolynomial φ P + observablePolynomial φ Q := by
        funext z; simp [observablePolynomial]
      rw [heq]; exact hP.add hQ
  | mul_X P i hP =>
      have heq : observablePolynomial φ (P * MvPolynomial.X i) = observablePolynomial φ P * φ i := by
        funext z; simp [observablePolynomial]
      rw [heq]; exact hP.mul (hφ i)

/-- Real Fréchet chain rule for complex polynomial observables. -/
theorem fderiv_observablePolynomial (φ : ι → E → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (Q : MvPolynomial ι ℂ) (z v : E) :
    fderiv ℝ (observablePolynomial φ Q) z v =
      ∑ i, observablePolynomial φ (MvPolynomial.pderiv i Q) z * fderiv ℝ (φ i) z v := by
  induction Q using MvPolynomial.induction_on with
  | C c =>
      have heq : observablePolynomial φ (MvPolynomial.C c) = fun _ => c := by
        funext z; simp [observablePolynomial]
      simp [heq, observablePolynomial]
  | add P Q hP hQ =>
      have heq : observablePolynomial φ (P + Q) = observablePolynomial φ P + observablePolynomial φ Q := by
        funext z; simp [observablePolynomial]
      rw [heq, fderiv_add ((differentiable_observablePolynomial φ hφ P) z)
        ((differentiable_observablePolynomial φ hφ Q) z)]
      simp only [ContinuousLinearMap.add_apply, hP, hQ, map_add, observablePolynomial,
        add_mul, Finset.sum_add_distrib]
  | mul_X P j hP =>
      have heq : observablePolynomial φ (P * MvPolynomial.X j) = observablePolynomial φ P * φ j := by
        funext z; simp [observablePolynomial]
      rw [heq, fderiv_mul ((differentiable_observablePolynomial φ hφ P) z) (hφ j z)]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        hP, smul_eq_mul, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
        observablePolynomial, map_add, map_mul, MvPolynomial.eval_X, add_mul,
        Finset.sum_add_distrib]
      simp [hP, observablePolynomial, Pi.single_apply, Finset.mul_sum, mul_assoc]
      ring

/-- The second directional derivative of a polynomial composite. -/
theorem second_fderiv_observablePolynomial (φ : ι → E → ℂ)
    (hφ : ∀ i, Differentiable ℝ (φ i)) (v : E)
    (hdφ : ∀ i, Differentiable ℝ (fun z => fderiv ℝ (φ i) z v))
    (Q : MvPolynomial ι ℂ) (z : E) :
    fderiv ℝ (fun w => fderiv ℝ (observablePolynomial φ Q) w v) z v =
      ∑ i, ((∑ j, observablePolynomial φ (MvPolynomial.pderiv j (MvPolynomial.pderiv i Q)) z *
          fderiv ℝ (φ j) z v) * fderiv ℝ (φ i) z v +
        observablePolynomial φ (MvPolynomial.pderiv i Q) z *
          fderiv ℝ (fun w => fderiv ℝ (φ i) w v) z v) := by
  have heq : (fun w => fderiv ℝ (observablePolynomial φ Q) w v) =
      fun w => ∑ i, observablePolynomial φ (MvPolynomial.pderiv i Q) w * fderiv ℝ (φ i) w v := by
    funext w; exact fderiv_observablePolynomial φ hφ Q w v
  rw [heq, fderiv_fun_sum]
  · simp only [sum_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [fderiv_fun_mul ((differentiable_observablePolynomial φ hφ _) z) (hdφ i z)]
    simp [fderiv_observablePolynomial φ hφ, add_comm, mul_comm]
  · intro i _
    exact ((differentiable_observablePolynomial φ hφ _) z).mul (hdφ i z)

/-- Formal mixed partial derivatives commute. -/
theorem polynomial_pderiv_commute (Q : MvPolynomial ι ℂ) (i j : ι) :
    MvPolynomial.pderiv j (MvPolynomial.pderiv i Q) =
      MvPolynomial.pderiv i (MvPolynomial.pderiv j Q) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P k hP =>
      simp only [MvPolynomial.pderiv_mul, map_add, MvPolynomial.pderiv_X,
        Pi.single_apply, apply_ite, MvPolynomial.pderiv_one, map_zero, hP]
      split_ifs <;> simp <;> ring

end
end
end GinibrePoincare
