module

public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators

namespace GinibrePoincare
noncomputable section

/-- Coordinatewise nonnegative integrable weights preserve product structure. -/
theorem pi_withDensity_ofReal_eq
    {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (μ : ι → Measure E) [∀ i, SigmaFinite (μ i)]
    (w : ι → E → ℝ) (_hw : ∀ i, Measurable (w i))
    (hi : ∀ i, Integrable (w i) (μ i)) (hp : ∀ i x, 0 ≤ w i x)
    [∀ i, SigmaFinite ((μ i).withDensity (fun x => ENNReal.ofReal (w i x)))] :
    Measure.pi (fun i => (μ i).withDensity (fun x => ENNReal.ofReal (w i x))) =
      (Measure.pi μ).withDensity (fun x => ENNReal.ofReal (∏ i, w i (x i))) := by
  apply Measure.pi_eq
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hir : ∀ i, Integrable (w i) ((μ i).restrict (s i)) :=
    fun i => (hi i).restrict
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hir)
    (ae_of_all _ (fun x => Finset.prod_nonneg (fun i _ => hp i (x i)))),
    integral_fintype_prod_eq_prod,
    ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hp i))]
  congr 1
  funext i
  rw [withDensity_apply _ (hs i)]
  exact ofReal_integral_eq_lintegral_ofReal (hir i) (ae_of_all _ (hp i))

end
end GinibrePoincare
