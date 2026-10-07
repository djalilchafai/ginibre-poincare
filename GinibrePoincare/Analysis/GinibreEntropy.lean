module

public import GinibrePoincare.Concrete.SmoothTarget
public import GinibrePoincare.Analysis.GinibreMassFiniteness
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
public import Mathlib.Analysis.Convex.Integral

@[expose] public section

/-! # Actual square entropy for the radial log-Sobolev problem
These are entropy and integrability results, not a log-Sobolev inequality.
-/
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Square entropy with its actual integral definition. -/
def squareEntropy {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) : ℝ :=
  (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) -
    (∫ x, f x ^ 2 ∂μ) * Real.log (∫ x, f x ^ 2 ∂μ)

/-- The entropy appearing in the paper, for the concrete Ginibre measure. -/
def ginibreSquareEntropy (n : ℕ) (f : Configuration n → ℝ) : ℝ :=
  squareEntropy (ginibreMeasure n) f

/-- Compact continuous observables have integrable squares. -/
theorem integrable_sq_ginibre {n : ℕ} (hn : 0 < n) {f : Configuration n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun z => f z ^ 2) (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  have hs : HasCompactSupport (fun z => f z ^ 2) := by
    apply hfc.mono
    intro z hz hzero
    apply hz
    simp [hzero]
  exact (hf.pow 2).integrable_of_hasCompactSupport hs

/-- At zeros of `f`, the expression `f² log f²` extends continuously by zero. -/
theorem continuous_square_mul_log {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : Continuous f) : Continuous (fun x => f x ^ 2 * Real.log (f x ^ 2)) :=
  Real.continuous_mul_log.comp (hf.pow 2)

/-- The logarithmic entropy integrand has the same compact-support bound as `f`. -/
theorem compactSupport_square_mul_log {α : Type*} [TopologicalSpace α] {f : α → ℝ}
    (hf : HasCompactSupport f) : HasCompactSupport (fun x => f x ^ 2 * Real.log (f x ^ 2)) := by
  apply hf.mono
  intro x hx hzero
  apply hx
  simp [hzero]

/-- Entropy is a genuine finite integral for smooth compact observables. -/
theorem integrable_square_mul_log_ginibre {n : ℕ} (hn : 0 < n) {f : Configuration n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun z => f z ^ 2 * Real.log (f z ^ 2)) (ginibreMeasure n) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (continuous_square_mul_log hf).integrable_of_hasCompactSupport
    (compactSupport_square_mul_log hfc)

/-- Jensen's inequality makes square entropy nonnegative for a probability law. -/
theorem squareEntropy_nonneg {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (f : α → ℝ) (hf : Integrable (fun x => f x ^ 2) μ)
    (hlog : Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) μ) :
    0 ≤ squareEntropy μ f := by
  have hj := Real.convexOn_mul_log.map_integral_le
    Real.continuous_mul_log.continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun x => sq_nonneg (f x))) hf hlog
  exact sub_nonneg.mpr hj

/-- Concrete square entropy is nonnegative on the smooth compact class. -/
theorem ginibreSquareEntropy_nonneg {n : ℕ} (hn : 0 < n) {f : Configuration n → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : 0 ≤ ginibreSquareEntropy n f := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact squareEntropy_nonneg _ f (integrable_sq_ginibre hn hf hfc)
    (integrable_square_mul_log_ginibre hn hf hfc)

/-- Entropy transfer under an actual image measure. -/
theorem squareEntropy_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (T : α → β) (hT : AEMeasurable T μ) (f : β → ℝ)
    (hsq : AEStronglyMeasurable (fun y => f y ^ 2) (μ.map T))
    (hlog : AEStronglyMeasurable (fun y => f y ^ 2 * Real.log (f y ^ 2)) (μ.map T)) :
    squareEntropy (μ.map T) f = squareEntropy μ (fun x => f (T x)) := by
  unfold squareEntropy
  rw [integral_map hT hsq, integral_map hT hlog]

/-- Equal square and logarithmic moments give equal entropy (the Kostlan transfer step). -/
theorem squareEntropy_eq_of_moments {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) (f : α → ℝ) (g : β → ℝ)
    (hsq : (∫ x, f x ^ 2 ∂μ) = ∫ y, g y ^ 2 ∂ν)
    (hlog : (∫ x, f x ^ 2 * Real.log (f x ^ 2) ∂μ) = ∫ y, g y ^ 2 * Real.log (g y ^ 2) ∂ν) :
    squareEntropy μ f = squareEntropy ν g := by
  simp only [squareEntropy, hsq, hlog]

end
end GinibrePoincare
