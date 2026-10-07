module

public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroLampertiRecovery
public import Mathlib.Probability.Independence.Basic

@[expose] public section

/-! Whole-process independence transfers from the center path to its recovered
punctured Lamperti driver. The hypotheses are actual increment identities. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreCenterPuncturedDriver_eq_recovery
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (n : ℕ) (α : ℝ)
    (S : Ω → ℝ≥0 → ℂ) (β : ℝ≥0 → Ω → ℝ)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (h0 : ∀ᵐ ω ∂P, β 0 ω = 0)
    (hi : ∀ᵐ ω ∂P, ∀ k t, ginibreCenterPositiveStart k ≤ t →
      ginibreCenterPositiveStartLamperti n α k (S ω) t =
        β t ω - β (ginibreCenterPositiveStart k) ω) :
    (fun ω t => β t ω) =ᵐ[P] (fun ω => ginibreCenterPuncturedLampertiRecovery n α (S ω)) := by
  filter_upwards [hc,h0,hi] with ω hc h0 hi
  exact (ginibreCenterPuncturedLampertiRecovery_eq n α (S ω) _ hc h0 hi).symm

theorem ginibreCenterPuncturedDriver_independent
    {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (P : Measure Ω) (n : ℕ) (α : ℝ) (S : Ω → ℝ≥0 → ℂ)
    (β : ℝ≥0 → Ω → ℝ) (R : Ω → E)
    (hind : IndepFun S R P)
    (hc : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (h0 : ∀ᵐ ω ∂P, β 0 ω = 0)
    (hi : ∀ᵐ ω ∂P, ∀ k t, ginibreCenterPositiveStart k ≤ t →
      ginibreCenterPositiveStartLamperti n α k (S ω) t =
        β t ω - β (ginibreCenterPositiveStart k) ω) :
    IndepFun (fun ω t => β t ω) R P := by
  exact (hind.comp (ginibreCenterPuncturedLampertiRecovery_measurable n α)
    measurable_id).congr
      (ginibreCenterPuncturedDriver_eq_recovery P n α S β hc h0 hi).symm
      Filter.EventuallyEq.rfl

#print axioms ginibreCenterPuncturedDriver_eq_recovery
#print axioms ginibreCenterPuncturedDriver_independent
end
end GinibrePoincare
