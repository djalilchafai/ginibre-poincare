module

public import GinibrePoincare.Analysis.TwoPointLSI

@[expose] public section

open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- A recursively presented finite Bernoulli cube. -/
def BernoulliCube : ℕ → Type
  | 0 => Unit
  | n + 1 => BernoulliCube n × Bool

instance bernoulliCubeFintype : (n : ℕ) → Fintype (BernoulliCube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 => @instFintypeProd (BernoulliCube n) Bool (bernoulliCubeFintype n) inferInstance

instance bernoulliCubeNonempty : (n : ℕ) → Nonempty (BernoulliCube n)
  | 0 => inferInstanceAs (Nonempty Unit)
  | n + 1 => @instNonemptyProd (BernoulliCube n) Bool (bernoulliCubeNonempty n) inferInstance

/-- The sum of the conditional two-point energies, with probability normalization. -/
def bernoulliCubeEnergy : (n : ℕ) → (BernoulliCube n → ℝ) → ℝ
  | 0, _ => 0
  | n + 1, f =>
      (∑ y : Bool, bernoulliCubeEnergy n (fun x => f (x, y))) / 2 +
      (∑ x : BernoulliCube n, (f (x, true) - f (x, false)) ^ 2 / 2) /
        Fintype.card (BernoulliCube n)

/-- Sharp logarithmic Sobolev inequality on every finite fair Bernoulli cube. -/
theorem bernoulliCube_lsi (n : ℕ) (f : BernoulliCube n → ℝ) :
    uniformFiniteEntropy (fun x => (f x) ^ 2) ≤ bernoulliCubeEnergy n f := by
  induction n with
  | zero =>
      change uniformFiniteEntropy (fun x : Unit => (f x) ^ 2) ≤ 0
      simp [uniformFiniteEntropy, Fintype.card_unique]
  | succ n ih =>
      have h := uniformFiniteLSI_tensorization (bernoulliCubeEnergy n)
        (fun f : Bool → ℝ => (f true - f false) ^ 2 / 2) ih uniformFiniteLSI_bool f
      change uniformFiniteEntropy (fun p : BernoulliCube n × Bool => (f p) ^ 2) ≤ _
      simpa [bernoulliCubeEnergy] using h

end
end GinibrePoincare
