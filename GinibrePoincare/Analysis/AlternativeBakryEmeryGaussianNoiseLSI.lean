module

public import GinibrePoincare.Analysis.GaussianFiniteIndexBoundedLSI
public import GinibrePoincare.Analysis.StrongConvexBoundedLipschitzLSIExtension
public import GinibrePoincare.Analysis.FinitePiDensity

@[expose] public section

/-! # The finite Gaussian-noise entropy input for the Langevin proof
The input covers bounded Lipschitz functions, so differentiability of the
entire stochastic flow in every Gaussian coordinate is not assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff
namespace GinibrePoincare
noncomputable section

/-- Absolute continuity of the actual finite Gaussian noise law. -/
theorem bakryEmeryGaussianNoise_absolutelyContinuous
    (I : Type*) [Fintype I] [DecidableEq I] (v : ℝ≥0) (hv : v ≠ 0) :
    Measure.pi (fun _ : I => gaussianReal 0 v) ≪ (volume : Measure (I → ℝ)) := by
  letI (i : I) : IsProbabilityMeasure (volume.withDensity (gaussianPDF 0 v)) := by
    rw [← gaussianReal_of_var_ne_zero 0 hv]
    infer_instance
  simp_rw [gaussianReal_of_var_ne_zero 0 hv]
  rw [Measure.pi_withDensity (fun _ : I => (volume : Measure ℝ))
    (fun _ : I => gaussianPDF 0 v) (fun _ => measurable_gaussianPDF 0 v), ← volume_pi]
  exact withDensity_absolutelyContinuous _ _

/-- Sharp LSI for bounded Lipschitz observables of any nonempty finite Gaussian
noise family, with the actual a.e. coordinate derivatives in its energy. -/
theorem bakryEmeryGaussianNoise_lsi_boundedLipschitz
    (I : Type*) [Fintype I] [DecidableEq I] [Nonempty I] (v : ℝ≥0) (hv : v ≠ 0)
    (f : (I → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (C : ℝ) (hb : ∀ x, |f x| ≤ C) :
    squareEntropy (Measure.pi (fun _ : I => gaussianReal 0 v)) f ≤
      (2 * (v : ℝ)) * ∫ x, directionalEnergy (fun i : I => Pi.single i 1) f x
        ∂Measure.pi (fun _ : I => gaussianReal 0 v) := by
  apply boundedLipschitz_lsi_of_C1 volume (Measure.pi (fun _ : I => gaussianReal 0 v))
    (bakryEmeryGaussianNoise_absolutelyContinuous I v hv)
    (fun i : I => Pi.single i 1) (2 * (v : ℝ)) _ f hf C
      (by simpa only [Real.norm_eq_abs] using hb)
  intro g hg L hL D hD
  have hD0 : 0 ≤ D := (norm_nonneg (g 0)).trans (hD 0)
  exact gaussianFiniteIndex_lsi_bounded_C1 I v g hg D (L : ℝ) hD0
    (by simpa only [Real.norm_eq_abs] using hD)
    (fun x => norm_fderiv_le_of_lipschitz ℝ hL)

#print axioms bakryEmeryGaussianNoise_absolutelyContinuous
#print axioms bakryEmeryGaussianNoise_lsi_boundedLipschitz

end
end GinibrePoincare
