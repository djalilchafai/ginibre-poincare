module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianQuadraticOrthogonality
public import GinibrePoincare.Analysis.GinibreStochasticBrownianWeightedQuadratic

@[expose] public section

/-! Finite square-moment expansion for genuinely orthogonal random errors. -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000

theorem ginibre_integral_square_sum_of_cross_zero {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] (P : Measure Ω)
    (X : ι → Ω → ℝ) (hX : ∀ i, MemLp (X i) 2 P)
    (hcross : ∀ i j, i ≠ j → (∫ ω, X i ω * X j ω ∂P) = 0) :
    (∫ ω, (∑ i, X i ω)^2 ∂P) = ∑ i, ∫ ω, (X i ω)^2 ∂P := by
  have hprod (i j : ι) : Integrable (fun ω => X i ω * X j ω) P :=
    (hX i).integrable_mul (hX j)
  have hsum (i : ι) : Integrable (fun ω => ∑ j, X i ω * X j ω) P :=
    integrable_finsetSum Finset.univ (fun j _ => hprod i j)
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finsetSum Finset.univ (fun i _ => hsum i)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (fun j _ => hprod i j)]
  rw [Finset.sum_eq_single i]
  · intro j hj hji
    exact hcross i j (Ne.symm hji)
  · simp

end
end GinibrePoincare
