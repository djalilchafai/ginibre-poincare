module

public import GinibrePoincare.Analysis.BrownianOrthogonalGaussianLaw
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem gaussianReal_standard_sqrt_map (v : ℝ≥0) :
    (gaussianReal 0 1).map (fun x => Real.sqrt (v : ℝ) * x) = gaussianReal 0 v := by
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero, mul_one]
  congr 1
  ext
  exact Real.sq_sqrt v.property

 theorem piGaussianReal_map_toLp_scaledStandard (ι : Type*) [Fintype ι] (v : ℝ≥0) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)).map (WithLp.toLp 2) =
      scaledStandardGaussian (EuclideanSpace ℝ ι) v := by
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
  let S := fun x : ι → ℝ => fun i => Real.sqrt (v : ℝ) * x i
  have hs : μ.map S = Measure.pi (fun _ : ι => gaussianReal 0 v) := by
    rw [Measure.pi_map_pi (fun _ => (by fun_prop))]
    simp_rw [gaussianReal_standard_sqrt_map]
  unfold scaledStandardGaussian
  rw [← map_pi_eq_stdGaussian]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rw [← hs, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

end
end GinibrePoincare
