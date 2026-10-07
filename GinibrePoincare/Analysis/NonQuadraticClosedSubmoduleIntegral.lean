module

public import Mathlib.Analysis.Normed.Group.Quotient
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! # Genuine Bochner integrals in closed linear subspaces -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 200000

/-- A Bochner integral of an actual integrable subspace-valued function
belongs to the same closed subspace. The quotient map proves this for
Banach spaces, including the product norm used by derivative graphs. -/
theorem bochner_integral_mem_closed_submodule
    {A H : Type*} [MeasurableSpace A]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (K : Submodule ℝ H) (hK : IsClosed (K : Set H)) (μ : Measure A)
    (f : A → H) (hf : Integrable f μ) (hmem : ∀ a, f a ∈ K) :
    (∫ a, f a ∂μ) ∈ K := by
  let : IsClosed (K : Set H) := hK
  have he : K.mkQL (∫ a, f a ∂μ) = 0 := by
    rw [← K.mkQL.integral_comp_comm hf]
    have hz : (fun a => K.mkQL (f a)) = 0 := by
      funext a
      exact (Submodule.Quotient.mk_eq_zero K).mpr (hmem a)
    rw [hz]
    change (∫ a, (0 : H ⧸ K) ∂μ) = 0
    exact integral_zero _ _
  exact (Submodule.Quotient.mk_eq_zero K).mp he
end
end GinibrePoincare
