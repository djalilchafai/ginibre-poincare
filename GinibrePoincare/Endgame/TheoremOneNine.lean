module

public import GinibrePoincare.Endgame.SeriesDeficit
public import GinibrePoincare.Endgame.GeneratorCompletion

@[expose] public section

/-!
# The two sum-of-squares identities of Theorem 1.9

This file joins the Hermite-series deficit calculation to the universal
generator square-completion. It is an abstract reduction: Parseval, zero-mode
geometry, and the mode energy formula are explicit hypotheses here.
`ConcreteTheoremOneNine.lean` realizes the quantities on the smooth core;
`FullTheoremOneNine.lean` exports the ordinary generator-domain theorem.

First `infinite_deficit_identity` rearranges Parseval and the zero-mode
Pythagorean identity. Then `completionSquare` rewrites the generator deficit
in terms of the first deficit. The remaining step is scalar polynomial algebra.
-/

namespace GinibrePoincare

noncomputable section

namespace TheoremOneNine

open OperatorSquareCompletion

variable {E : Type*}
variable [SeminormedAddCommGroup E]
variable [InnerProductSpace ℝ E]

/-- Abstract, fully checked form of both identities in Theorem 1.9 of
http://arxiv.org/abs/2608.19358v2. -/
theorem sum_of_squares
    (A : E →ₗ[ℝ] E) (f : E)
    (a : ℕ → ℝ) (holomorphicSq remainderSq : ℝ)
    (ha : Summable a)
    (ht : Summable fun k : ℕ => (k : ℝ) * a k)
    (hParseval :
      variance f = holomorphicSq + modeMass a)
    (hGeometry :
      variance f = 2 * holomorphicSq + remainderSq)
    (hEnergy :
      energy A f = 4 * modeEnergy a) :
    (energy A f - 2 * variance f =
      2 * remainderSq + 4 * modeTail a) ∧
    (generatorSq A f - 2 * energy A f =
      shiftedGeneratorSq A f +
        4 * remainderSq + 8 * modeTail a) := by
  have hDeficit :
      energy A f - 2 * variance f =
        2 * remainderSq + 4 * modeTail a :=
    infinite_deficit_identity a ha ht
      (variance f) holomorphicSq remainderSq (energy A f)
      hParseval hGeometry hEnergy
  constructor
  · exact hDeficit
  · rw [completionSquare A f, hDeficit]
    ring

end TheoremOneNine

end

end GinibrePoincare
