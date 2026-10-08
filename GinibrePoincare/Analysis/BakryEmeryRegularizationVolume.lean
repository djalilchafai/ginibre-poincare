module

public import GinibrePoincare.Analysis.BakryEmeryRegularizationLimit
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

@[expose] public section

/-! Gaussian domination and Gibbs regularization on actual Euclidean volume. -/
namespace GinibrePoincare
open MeasureTheory
open scoped Topology
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/-- The confinement majorant is genuinely integrable in every finite real
Hilbert dimension, including the block dimensions of Theorem 1.14. -/
theorem bakryEmery_gaussian_majorant_integrable (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : E => Real.exp (-a*‖x‖^2)) volume := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
    (V := E) (b := (a:ℂ)) (by simpa using ha) 0 (0:E)).re
  convert h using 1
  funext x
  simp only [neg_mul, zero_mul, add_zero]
  change Real.exp (-(a*‖x‖^2)) = (Complex.exp (-((a:ℂ)*(‖x‖:ℂ)^2))).re
  rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_neg, Complex.exp_ofReal_re]

/-- Concrete compact-test entropy convergence on actual Euclidean volume:
the Gaussian integrability input is discharged internally. -/
theorem bakryEmeryRegularizedLift_volume_entropy_tendsto
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : E → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Filter.Tendsto (fun ε : ℝ => squareEntropy (bakryEmeryNormalizedGibbs volume
      (bakryEmeryRegularizedLiftPotential n V ε)) f) (𝓝 0)
      (𝓝 (squareEntropy (bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V)) f)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  exact bakryEmeryRegularizedLift_entropy_tendsto volume n ρ V hV hρ.le hrot hc
    (by simpa only [neg_div] using
      bakryEmery_gaussian_majorant_integrable (E := E) ((n:ℝ)*ρ/2) (by positivity)) f hf hfc

/-- Concrete compact-test expectations converge under the actual volume laws. -/
theorem bakryEmeryRegularizedLift_volume_expectation_tendsto
    (n : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ) (V : Potential)
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : E → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    Filter.Tendsto (fun ε : ℝ => ∫ x, f x ∂bakryEmeryNormalizedGibbs volume
      (bakryEmeryRegularizedLiftPotential n V ε)) (𝓝 0)
      (𝓝 (∫ x, f x ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryEuclideanLiftPotential n V))) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  exact bakryEmeryRegularizedLift_compact_expectation_tendsto volume n ρ V hV hρ.le hrot hc
    (by simpa only [neg_div] using
      bakryEmery_gaussian_majorant_integrable (E := E) ((n:ℝ)*ρ/2) (by positivity)) f hf hfc

#print axioms bakryEmery_gaussian_majorant_integrable
#print axioms bakryEmeryRegularizedLift_volume_entropy_tendsto
#print axioms bakryEmeryRegularizedLift_volume_expectation_tendsto
end
end GinibrePoincare
