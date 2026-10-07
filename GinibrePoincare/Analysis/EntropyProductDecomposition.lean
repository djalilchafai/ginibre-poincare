module

public import GinibrePoincare.Analysis.GinibreEntropy
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The square moment of a fiber in a product probability space. -/
def fiberSquareMoment {α β : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : α × β → ℝ) (x : α) : ℝ := ∫ y, f (x, y) ^ 2 ∂ν

theorem fiberSquareMoment_nonneg {α β : Type*} [MeasurableSpace β]
    (ν : Measure β) (f : α × β → ℝ) (x : α) : 0 ≤ fiberSquareMoment ν f x :=
  integral_nonneg (fun y => sq_nonneg (f (x, y)))

/-- The exact chain decomposition of square entropy under a product law.
This is the algebraic/measure-theoretic tensorization step; it is not an LSI.
The logarithmic fiber moment is an explicit integrability condition. -/
theorem squareEntropy_prod_decomposition
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SigmaFinite μ] [SigmaFinite ν]
    (f : α × β → ℝ)
    (hsq : Integrable (fun p => f p ^ 2) (μ.prod ν))
    (hlog : Integrable (fun p => f p ^ 2 * Real.log (f p ^ 2)) (μ.prod ν))
    (hfiber : Integrable (fun x => fiberSquareMoment ν f x *
      Real.log (fiberSquareMoment ν f x)) μ) :
    squareEntropy (μ.prod ν) f =
      (∫ x, squareEntropy ν (fun y => f (x, y)) ∂μ) +
        squareEntropy μ (fun x => Real.sqrt (fiberSquareMoment ν f x)) := by
  have hsqrt : ∀ x, Real.sqrt (fiberSquareMoment ν f x) ^ 2 = fiberSquareMoment ν f x :=
    fun x => Real.sq_sqrt (fiberSquareMoment_nonneg ν f x)
  have him : Integrable
      (fun x => ∫ y, f (x, y) ^ 2 * Real.log (f (x, y) ^ 2) ∂ν) μ :=
    hlog.integral_prod_left
  unfold squareEntropy
  simp only [hsqrt]
  change _ = (∫ x, (∫ y, f (x, y) ^ 2 * Real.log (f (x, y) ^ 2) ∂ν) -
      fiberSquareMoment ν f x * Real.log (fiberSquareMoment ν f x) ∂μ) + _
  rw [integral_sub him hfiber, integral_prod (fun p => f p ^ 2 * Real.log (f p ^ 2)) hlog]
  have hm : (∫ x, fiberSquareMoment ν f x ∂μ) = ∫ p, f p ^ 2 ∂μ.prod ν :=
    (integral_prod (fun p => f p ^ 2) hsq).symm
  rw [hm]
  ring

end
end GinibrePoincare
