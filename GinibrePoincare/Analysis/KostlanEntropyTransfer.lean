module

public import GinibrePoincare.Analysis.KostlanGammaLaw
public import GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The independent Gamma law of the scaled squared individual radii. -/
def kostlanGammaProduct (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i : Fin n => ProbabilityTheory.gammaMeasure ((i.val + 1 : ℕ) : ℝ) 1)

/-- The actual square entropy transfers to the independent Gamma product. -/
theorem ginibre_radial_entropy_eq_gamma_product (n : ℕ) (hn : 0 < n)
    (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) (hc : HasCompactSupport F)
    (hS : IsSymmetricRadiusTest n F) :
    ginibreSquareEntropy n (fun z => F (fun i => kostlanSquaredRadius n (z i))) =
      squareEntropy (kostlanGammaProduct n) F := by
  apply squareEntropy_eq_of_moments
  · have hs : HasCompactSupport (fun r => F r ^ 2) := by
      apply hc.mono
      intro r hr hz
      exact hr (by simp [hz])
    obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous (hF.pow 2)
    exact ginibre_radial_expectation_eq_gamma_product n hn (fun r => F r ^ 2)
      (hF.pow 2) (by intro σ r; dsimp; rw [hS σ r]) C hC
  · obtain ⟨C, hC⟩ := (compactSupport_square_mul_log hc).exists_bound_of_continuous
      (continuous_square_mul_log hF)
    exact ginibre_radial_expectation_eq_gamma_product n hn
      (fun r => F r ^ 2 * Real.log (F r ^ 2)) (continuous_square_mul_log hF)
      (by intro σ r; dsimp; rw [hS σ r]) C hC

end
end GinibrePoincare
