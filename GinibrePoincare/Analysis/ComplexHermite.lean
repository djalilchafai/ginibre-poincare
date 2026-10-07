module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Complex.Basic

@[expose] public section

/-!
# Univariate complex Hermite polynomials: algebraic layer

This file defines the two-variable polynomial underlying the complex Hermite
system.  The parameter `ρ` is the variance.  Thus the polynomial is

`J p q ρ = ∑ k, (-ρ)^k k! (p choose k) (q choose k) z^(p-k) w^(q-k)`.

Substitution `w = conj z` gives the usual univariate complex Hermite
polynomial.  Keeping the two formal variables separate makes the Wirtinger
operators honest partial derivatives.
-/

namespace GinibrePoincare

open scoped BigOperators ComplexConjugate

/-- The two formal coordinates `z` and `w` (later specialized to `z` and
`conj z`). -/
abbrev ComplexHermiteIndex := Fin 2

namespace ComplexHermite

abbrev Poly := MvPolynomial ComplexHermiteIndex ℂ

/-- Formal holomorphic coordinate. -/
noncomputable def Z : Poly := MvPolynomial.X 0

/-- Formal antiholomorphic coordinate. -/
noncomputable def W : Poly := MvPolynomial.X 1

/-- The unnormalized complex Hermite polynomial of bidegree `(p,q)` and
variance `ρ`. -/
noncomputable def raw (ρ : ℝ) (p q : ℕ) : Poly :=
  ∑ k ∈ Finset.range (min p q + 1),
    MvPolynomial.C (((-(ρ : ℂ)) ^ k) * (k.factorial : ℂ) *
      (Nat.choose p k : ℂ) * (Nat.choose q k : ℂ)) *
      Z ^ (p - k) * W ^ (q - k)

/-- Evaluation of the formal polynomial on the complex diagonal
`(z, conj z)`. -/
noncomputable def eval (ρ : ℝ) (p q : ℕ) (z : ℂ) : ℂ :=
  MvPolynomial.eval ![z, conj z] (raw ρ p q)

@[simp] theorem raw_zero_right (ρ : ℝ) (p : ℕ) : raw ρ p 0 = Z ^ p := by
  simp [raw]

@[simp] theorem raw_zero_left (ρ : ℝ) (q : ℕ) : raw ρ 0 q = W ^ q := by
  simp [raw]

@[simp] theorem raw_zero_zero (ρ : ℝ) : raw ρ 0 0 = 1 := by
  simp

@[simp] theorem eval_zero_right (ρ : ℝ) (p : ℕ) (z : ℂ) :
    eval ρ p 0 z = z ^ p := by
  simp [eval, Z]

@[simp] theorem eval_zero_left (ρ : ℝ) (q : ℕ) (z : ℂ) :
    eval ρ 0 q z = (conj z) ^ q := by
  simp [eval, W]

@[simp] theorem eval_zero_zero (ρ : ℝ) (z : ℂ) : eval ρ 0 0 z = 1 := by
  simp

/-- The first mixed complex Hermite polynomial is `zw - ρ`. -/
theorem raw_one_one (ρ : ℝ) : raw ρ 1 1 = Z * W - MvPolynomial.C (ρ : ℂ) := by
  norm_num [raw, Z, W, Finset.sum_range_succ]
  ring

theorem eval_one_one (ρ : ℝ) (z : ℂ) :
    eval ρ 1 1 z = z * conj z - ρ := by
  rw [eval, raw_one_one]
  simp [Z, W]

/-- On the holomorphic axis the formal antiholomorphic derivative vanishes. -/
theorem pderiv_W_raw_zero_right (ρ : ℝ) (p : ℕ) :
    MvPolynomial.pderiv (1 : ComplexHermiteIndex) (raw ρ p 0) = 0 := by
  simp [raw_zero_right, Z]

/-- On the antiholomorphic axis the formal holomorphic derivative vanishes. -/
theorem pderiv_Z_raw_zero_left (ρ : ℝ) (q : ℕ) :
    MvPolynomial.pderiv (0 : ComplexHermiteIndex) (raw ρ 0 q) = 0 := by
  simp [raw_zero_left, W]

/-- Formal holomorphic differentiation on the holomorphic axis. -/
theorem pderiv_Z_raw_zero_right (ρ : ℝ) (p : ℕ) :
    MvPolynomial.pderiv (0 : ComplexHermiteIndex) (raw ρ p 0) =
      (p : Poly) * Z ^ (p - 1) := by
  simp [raw_zero_right, Z]

/-- Formal antiholomorphic differentiation on the antiholomorphic axis. -/
theorem pderiv_W_raw_zero_left (ρ : ℝ) (q : ℕ) :
    MvPolynomial.pderiv (1 : ComplexHermiteIndex) (raw ρ 0 q) =
      (q : Poly) * W ^ (q - 1) := by
  simp [raw_zero_left, W]

end ComplexHermite
end GinibrePoincare
