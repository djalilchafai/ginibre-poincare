module
public import GinibrePoincare.Analysis.CorrespondenceGUECenterGaussian
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueCenterCoordinate_contDiff (n : ℕ) : ContDiff ℝ ∞ (gueCenterCoordinate n) :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n)).contDiff

theorem gueCenterCoordinate_memLp {n : ℕ} (hn : 0<n) : MemLp (gueCenterCoordinate n) 2 (gueFullMeasure n) := by
  exact (IsGaussian.memLp_id (gaussianReal 0 (gueCenterVariance n)) 2 (by finiteness)).comp_measurePreserving
    (gueCenterCoordinate_measurePreserving hn)

theorem gueCenterCoordinate_gradient (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    gradient (gueCenterCoordinate n) x=gueCenterUnit n := by
  unfold gradient
  change (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n)) (gueCenterUnit n)) x)=gueCenterUnit n
  rw [ContinuousLinearMap.fderiv]
  simp

theorem gueCenterCoordinate_gradient_memLp {n : ℕ} (hn : 0<n) :
    MemLp (gradient (gueCenterCoordinate n)) 2 (gueFullMeasure n) := by
  letI := gueFullMeasure_probability hn
  have he : gradient (gueCenterCoordinate n)=fun _ => gueCenterUnit n := funext (gueCenterCoordinate_gradient n)
  rw [he]
  exact memLp_const (μ := gueFullMeasure n) (p := 2) (gueCenterUnit n)

theorem gueCenterCoordinate_poincare_equality {n : ℕ} (hn : 0<n) :
    (∫x, gueCenterCoordinate n x^2 ∂gueFullMeasure n)-
      (∫x, gueCenterCoordinate n x ∂gueFullMeasure n)^2=
    (1/(n : ℝ))*(∫x, ‖gradient (gueCenterCoordinate n) x‖^2 ∂gueFullMeasure n) := by
  letI := gueFullMeasure_probability hn
  rw [gueFullMeasure_center_gaussian_integral hn (fun t => t^2),
    gueFullMeasure_center_gaussian_integral hn (fun t => t)]
  simp only [integral_id_gaussianReal, zero_pow (by decide : 2≠0), sub_zero,
    gueCenterCoordinate_gradient, gueCenterUnit_norm hn, one_pow, integral_const, probReal_univ, smul_eq_mul, mul_one]
  have hv := variance_fun_id_gaussianReal (μ := 0) (v := gueCenterVariance n)
  rw [variance_eq_integral (X := fun x : ℝ => x) (by fun_prop)] at hv
  simp only [integral_id_gaussianReal, sub_zero] at hv
  rw [show (gueCenterVariance n : ℝ)=(n : ℝ)⁻¹ from rfl] at hv
  simpa only [one_div] using hv

#print axioms gueCenterCoordinate_poincare_equality
#print axioms gueCenterCoordinate_memLp
#print axioms gueCenterCoordinate_gradient_memLp
end
end GinibrePoincare
