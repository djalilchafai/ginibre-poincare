module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltVector
public import GinibrePoincare.Analysis.BrownianIntegralGaussianTiltLaw
public import Mathlib.Data.ENNReal.BigOperators

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

/-- Exact simultaneous tilt of every independent Gaussian coordinate. -/
theorem gaussianReal_pi_exponential_tilt {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
      (fun x => ENNReal.ofReal (gaussianVectorExponentialTilt h v x)) =
      Measure.pi (fun i => gaussianReal (h i*(v : ℝ)) v) := by
  classical
  apply (Measure.pi_eq (μ:=fun i => gaussianReal (h i*(v : ℝ)) v) ?_).symm
  intro s hs
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi]
  have hInt (i : ι) : Integrable (gaussianExponentialTilt (h i) v) ((gaussianReal 0 v).restrict (s i)) :=
    (gaussianExponentialTilt_integrable (h i) v).mono_measure Measure.restrict_le_self
  have hprod : Integrable (gaussianVectorExponentialTilt h v)
      (Measure.pi (fun i => (gaussianReal 0 v).restrict (s i))) := Integrable.fintype_prod_dep hInt
  rw [← ofReal_integral_eq_lintegral_ofReal hprod
    (Eventually.of_forall (gaussianVectorExponentialTilt_nonneg h v))]
  unfold gaussianVectorExponentialTilt
  rw [integral_fintype_prod_eq_prod]
  have hp : ∀ i ∈ (Finset.univ : Finset ι),
      0≤∫ x in s i, gaussianExponentialTilt (h i) v x ∂gaussianReal 0 v := by
    intro i hi
    exact integral_nonneg (fun x => (show 0≤gaussianExponentialTilt (h i) v x from (Real.exp_pos _).le))
  rw [ENNReal.ofReal_prod_of_nonneg hp]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← gaussianReal_exponential_tilt (h i) v, withDensity_apply _ (hs i),
    ← ofReal_integral_eq_lintegral_ofReal (hInt i)
      (Eventually.of_forall fun x => (Real.exp_pos _).le)]

/-- Under the true Gaussian RN tilt, subtracting the predictable drift restores
all centered independent coordinate laws. -/
theorem gaussianReal_pi_exponential_tilt_centered {ι : Type*} [Fintype ι]
    (h : ι → ℝ) (v : ℝ≥0) :
    ((Measure.pi (fun _ : ι => gaussianReal 0 v)).withDensity
      (fun x => ENNReal.ofReal (gaussianVectorExponentialTilt h v x))).map
      (fun x i => x i-h i*(v : ℝ)) = Measure.pi (fun _ : ι => gaussianReal 0 v) := by
  rw [gaussianReal_pi_exponential_tilt]
  have hmap (i : ι) : (gaussianReal (h i*(v : ℝ)) v).map
      (fun x : ℝ => x-h i*(v : ℝ)) = gaussianReal 0 v := by
    simpa only [sub_eq_add_neg, neg_mul, add_neg_cancel] using
      (gaussianReal_map_add_const (μ:=h i*(v : ℝ)) (v:=v) (-h i*(v : ℝ)))
  letI : ∀ i, IsProbabilityMeasure ((gaussianReal (h i*(v : ℝ)) v).map
      (fun x : ℝ => x-h i*(v : ℝ))) := fun i => by rw [hmap]; infer_instance
  rw [Measure.pi_map_pi (fun i => (show Measurable (fun x : ℝ => x-h i*(v : ℝ)) by fun_prop).aemeasurable)]
  simp_rw [hmap]

end
end GinibrePoincare
