module

public import GinibrePoincare.Analysis.BernoulliTaylorEnergy

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Sum of the actual fair signs in the recursive finite cube. -/
def bernoulliCubeSum : (n : ℕ) → BernoulliCube n → ℝ
  | 0, _ => 0
  | n + 1, p => bernoulliCubeSum n p.1 + if p.2 then 1 else -1

/-- Expectation under the uniform law on the finite cube. -/
def bernoulliCubeAverage (n : ℕ) (f : BernoulliCube n → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card (BernoulliCube n)

theorem bernoulliCube_card (n : ℕ) : Fintype.card (BernoulliCube n) = 2 ^ n := by
  induction n with
  | zero => change Fintype.card Unit = 1; simp
  | succ n ih =>
      change Fintype.card (BernoulliCube n × Bool) = _
      simp [ih, pow_succ]

theorem bernoulliCubeAverage_succ (n : ℕ) (f : BernoulliCube (n + 1) → ℝ) :
    bernoulliCubeAverage (n + 1) f =
      (bernoulliCubeAverage n (fun x => f (x, true)) +
        bernoulliCubeAverage n (fun x => f (x, false))) / 2 := by
  unfold bernoulliCubeAverage
  change (∑ p : BernoulliCube n × Bool, f p) / Fintype.card (BernoulliCube n × Bool) = _
  erw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat,
    Finset.sum_add_distrib]
  ring

/-- The conditional energy of a sum test has exactly one identical contribution per coordinate. -/
theorem bernoulliCubeEnergy_sum_test (n : ℕ) (f : ℝ → ℝ) :
    bernoulliCubeEnergy (n + 1) (fun x => f (bernoulliCubeSum (n + 1) x)) =
      ((n : ℝ) + 1) / 2 * bernoulliCubeAverage n
        (fun x => (f (bernoulliCubeSum n x + 1) - f (bernoulliCubeSum n x - 1)) ^ 2) := by
  induction n generalizing f with
  | zero =>
      unfold bernoulliCubeEnergy
      simp [bernoulliCubeAverage, bernoulliCubeSum, BernoulliCube, bernoulliCubeEnergy]
      ring
  | succ n ih =>
      change ((∑ y : Bool, bernoulliCubeEnergy (n + 1)
          (fun x => f (bernoulliCubeSum (n + 1) x + if y then 1 else -1))) / 2 +
        (∑ x : BernoulliCube (n + 1),
          (f (bernoulliCubeSum (n + 1) x + 1) - f (bernoulliCubeSum (n + 1) x + -1)) ^ 2 / 2) /
            Fintype.card (BernoulliCube (n + 1))) = _
      simp only [Fintype.sum_bool, Bool.false_eq_true, ite_true, ite_false]
      rw [ih (fun t => f (t + 1)), ih (fun t => f (t + -1))]
      have he : (∑ x : BernoulliCube (n + 1),
          (f (bernoulliCubeSum (n + 1) x + 1) - f (bernoulliCubeSum (n + 1) x + -1)) ^ 2 / 2) /
            Fintype.card (BernoulliCube (n + 1)) =
          bernoulliCubeAverage (n + 1)
            (fun x => (f (bernoulliCubeSum (n + 1) x + 1) - f (bernoulliCubeSum (n + 1) x - 1)) ^ 2) / 2 := by
        simp only [bernoulliCubeAverage, ← Finset.sum_div, sub_eq_add_neg]
        ring
      rw [he, bernoulliCubeAverage_succ]
      simp only [bernoulliCubeSum, Bool.false_eq_true, ite_true, ite_false, Nat.cast_add, Nat.cast_one]
      have h1 : (fun x : BernoulliCube n =>
          (f (bernoulliCubeSum n x + 1 + 1) - f (bernoulliCubeSum n x - 1 + 1)) ^ 2) =
        (fun x => (f (bernoulliCubeSum n x + 1 + 1) - f (bernoulliCubeSum n x + 1 - 1)) ^ 2) := by
        funext x
        congr 2 <;> ring
      have h2 : (fun x : BernoulliCube n =>
          (f (bernoulliCubeSum n x + 1 + -1) - f (bernoulliCubeSum n x - 1 + -1)) ^ 2) =
        (fun x => (f (bernoulliCubeSum n x + -1 + 1) - f (bernoulliCubeSum n x + -1 - 1)) ^ 2) := by
        funext x
        congr 2 <;> ring
      rw [h1, h2]
      ring

end
end GinibrePoincare
