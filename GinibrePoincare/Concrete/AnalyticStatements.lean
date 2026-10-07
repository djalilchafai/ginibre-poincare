module

public import GinibrePoincare.Concrete.HolomorphicDistance
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Exact analytic statements remaining in the main proof

Each proposition is written using the concrete measures, derivatives, and
normalized ground-state transform.  None is bundled into a certificate and
none is postulated by a declaration.
-/

namespace GinibrePoincare

noncomputable section

/-- The transformed centered observable belongs to the Gaussian `∂̄` domain. -/
def GroundStateAdmissibilityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    MeasureTheory.IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      IsGaussianDbarAdmissible n
        (normalizedVandermondeTransform n
          (fun z => (centeredObservable n f z : ℂ)))

/-- The Dirichlet-form identity after normalized multiplication by `V_n`. -/
def GroundStateEnergyIdentityStatement : Prop :=
  ∀ n : ℕ, 0 < n →
    MeasureTheory.IsProbabilityMeasure (ginibreMeasure n) →
    ∀ f : Configuration n → ℝ,
      IsSmoothCompactSymmetric f →
      smoothGinibreEnergy n f =
        4 * gaussianDbarEnergy n
          (normalizedVandermondeTransform n
            (fun z => (centeredObservable n f z : ℂ)))


end

end GinibrePoincare
