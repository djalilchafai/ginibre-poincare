module

public import GinibrePoincare.Analysis.BrownianOrthogonalPiGaussianLaw

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem scaledStandardGaussian_toPi (ι : Type*) [Fintype ι] (v : ℝ≥0) :
    (scaledStandardGaussian (EuclideanSpace ℝ ι) v).map
      (fun x : EuclideanSpace ℝ ι => fun i => x i) =
      Measure.pi (fun _ : ι => gaussianReal 0 v) := by
  rw [← piGaussianReal_map_toLp_scaledStandard ι v]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  exact Measure.map_id

theorem isotropicGaussian_coordinates_independent {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (v : ℝ≥0) (X : Ω → EuclideanSpace ℝ ι)
    (hX : HasLaw X (scaledStandardGaussian (EuclideanSpace ℝ ι) v) P) :
    (∀ i, HasLaw (fun ω => X ω i) (gaussianReal 0 v) P) ∧
      iIndepFun (fun i ω => X ω i) P := by
  have hp : HasLaw (fun ω i => X ω i) (Measure.pi (fun _ : ι => gaussianReal 0 v)) P :=
    (show HasLaw (fun x : EuclideanSpace ℝ ι => fun i => x i)
      (Measure.pi (fun _ : ι => gaussianReal 0 v))
      (scaledStandardGaussian (EuclideanSpace ℝ ι) v) from
        ⟨by fun_prop, scaledStandardGaussian_toPi ι v⟩).fun_comp hX
  have hi (i : ι) : HasLaw (fun ω => X ω i) (gaussianReal 0 v) P :=
    (measurePreserving_eval (fun _ : ι => gaussianReal 0 v) i).comp_hasLaw hp
  exact ⟨hi, (iIndepFun_iff_hasLaw_pi_pi hi).mpr hp⟩

end
end GinibrePoincare
