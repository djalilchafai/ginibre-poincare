module

public import GinibrePoincare.Analysis.AlternativeBakryEmeryRadialLift
public import GinibrePoincare.Analysis.GinibreSpatialCutoffs

@[expose] public section

/-! # Exact entropy and Dirichlet transfer through the Euclidean radius lift -/

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- Entropy is exactly preserved by the normalized Euclidean radius lift. -/
theorem bakryEmeryBlockLift_entropy (n k : ℕ) {V : Potential} (hV : Continuous V)
    (F : ℝ → ℝ) (hF : Continuous F) :
    squareEntropy (bakryEmeryBlockLift n k V)
      (fun x => F (gaussianBlockRadius 1 (k + 1) x)) =
    squareEntropy (potentialSquaredRadiusLaw n k V) F := by
  rw [← bakryEmeryBlockLift_squaredRadius n k hV]
  exact (squareEntropy_map _ _
    (continuous_gaussianBlockRadius 1 (k + 1)).measurable.aemeasurable F
    (hF.pow 2).aestronglyMeasurable
    (continuous_square_mul_log hF).aestronglyMeasurable).symm

/-- Exact ordinary Euclidean gradient of a smooth squared-radius profile. -/
theorem bakryEmeryBlockLift_gradient (k : ℕ) (F : ℝ → ℝ)
    (hF : Differentiable ℝ F) (x : Configuration (k + 1)) :
    ginibreEuclideanGradient (fun y => F (gaussianBlockRadius 1 (k + 1) y)) x =
      deriv F (configurationNormSq x) • ginibreEuclideanGradient configurationNormSq x := by
  ext j
  simp only [ginibreEuclideanGradient_coordinate, PiLp.smul_apply, smul_eq_mul]
  have he := (hF (configurationNormSq x)).hasDerivAt.comp_hasFDerivAt x
    (contDiff_configurationNormSq.differentiable (by simp)).differentiableAt.hasFDerivAt
  change fderiv ℝ (fun y => F (gaussianBlockRadius 1 (k + 1) y)) x _ = _
  simp only [gaussianBlockRadius, Nat.cast_one, one_mul]
  change fderiv ℝ (F ∘ configurationNormSq) x _ = _
  rw [he.fderiv]
  rfl

/-- Exact pointwise Dirichlet energy, including the factor four for squared radii. -/
theorem bakryEmeryBlockLift_gradient_norm_sq (k : ℕ) (F : ℝ → ℝ)
    (hF : Differentiable ℝ F) (x : Configuration (k + 1)) :
    ‖ginibreEuclideanGradient (fun y => F (gaussianBlockRadius 1 (k + 1) y)) x‖ ^ 2 =
      4 * configurationNormSq x * deriv F (configurationNormSq x) ^ 2 := by
  rw [bakryEmeryBlockLift_gradient k F hF, norm_smul, mul_pow,
    Real.norm_eq_abs, sq_abs, configurationNormSq_gradient_norm_sq]
  ring

/-- Integrated Dirichlet energy is exactly the one-dimensional weighted
squared-radius energy under the actual nonquadratic radius law. -/
theorem bakryEmeryBlockLift_energy (n k : ℕ) {V : Potential} (hV : Continuous V)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 1 F) :
    (∫ x, ‖ginibreEuclideanGradient
      (fun y => F (gaussianBlockRadius 1 (k + 1) y)) x‖ ^ 2 ∂bakryEmeryBlockLift n k V) =
      ∫ s, 4 * s * deriv F s ^ 2 ∂potentialSquaredRadiusLaw n k V := by
  simp_rw [bakryEmeryBlockLift_gradient_norm_sq k F (hF.differentiable (by norm_num))]
  rw [← bakryEmeryBlockLift_squaredRadius n k hV,
    integral_map (continuous_gaussianBlockRadius 1 (k + 1)).measurable.aemeasurable]
  · simp only [gaussianBlockRadius, Nat.cast_one, one_mul]
  · have hd : Continuous (deriv F) :=
      (show ContDiff ℝ (0 + 1) F from hF).deriv'.continuous
    exact ((continuous_const.mul continuous_id).mul (hd.pow 2)).aestronglyMeasurable

theorem continuous_bakryEmeryLiftSquaredRadii (n : ℕ) :
    Continuous (bakryEmeryLiftSquaredRadii n) := by
  apply continuous_pi
  intro i
  exact (continuous_gaussianBlockRadius 1 (i.val + 1)).comp (continuous_apply i)

/-- Exact entropy correspondence for the entire Euclidean block product. -/
theorem bakryEmeryProductLift_entropy (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    squareEntropy (bakryEmeryProductLift n V) (fun x => F (bakryEmeryLiftSquaredRadii n x)) =
      squareEntropy (potentialSquaredRadiusProduct n V) F := by
  rw [← bakryEmeryProductLift_squaredRadii n hn hV hrot hfin]
  exact (squareEntropy_map _ _ (continuous_bakryEmeryLiftSquaredRadii n).measurable.aemeasurable F
    (hF.pow 2).aestronglyMeasurable
    (continuous_square_mul_log hF).aestronglyMeasurable).symm

/-- Exact entropy transfer from the interacting nonquadratic law to the
paper's Euclidean lift, on its smooth compact symmetric radial profiles. -/
theorem bakryEmery_potential_entropy_eq_lift (n : ℕ) (hn : 0 < n)
    {V : Potential} (hV : Continuous V) (hrot : IsRotationalPotential V)
    (hfin : potentialPartition n V < ⊤) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) (hc : HasCompactSupport F) (hs : IsSymmetricRadiusTest n F) :
    squareEntropy (potentialMeasure n V) (fun z => F (fun i => Complex.normSq (z i))) =
      squareEntropy (bakryEmeryProductLift n V) (fun x => F (bakryEmeryLiftSquaredRadii n x)) := by
  rw [potential_radial_entropy_eq_squaredRadiusProduct n hn hV hrot hfin F hF hc hs,
    bakryEmeryProductLift_entropy n hn hV hrot hfin F hF]

#print axioms continuous_bakryEmeryLiftSquaredRadii
#print axioms bakryEmeryProductLift_entropy
#print axioms bakryEmery_potential_entropy_eq_lift

#print axioms bakryEmeryBlockLift_entropy
#print axioms bakryEmeryBlockLift_gradient
#print axioms bakryEmeryBlockLift_gradient_norm_sq
#print axioms bakryEmeryBlockLift_energy

end
end GinibrePoincare
