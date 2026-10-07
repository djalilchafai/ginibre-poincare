module

public import GinibrePoincare.Analysis.GinibreWeakGradient
public import Mathlib.Topology.Algebra.Module.Equiv

@[expose] public section

/-! # Covariance of the concrete gradient under particle relabelling -/

open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem permute_realCoordinateDirection {n : ℕ} (σ : ParticlePermutation n)
    (i : Fin n) : permute σ (realCoordinateDirection i) =
      realCoordinateDirection (σ.symm i) := by
  ext j
  simp [permute, realCoordinateDirection, coordinateDirection, Equiv.eq_symm_apply]

theorem permute_imaginaryCoordinateDirection {n : ℕ} (σ : ParticlePermutation n)
    (i : Fin n) : permute σ (imaginaryCoordinateDirection i) =
      imaginaryCoordinateDirection (σ.symm i) := by
  ext j
  simp [permute, imaginaryCoordinateDirection, coordinateDirection, Equiv.eq_symm_apply]

/-- The Euclidean gradient of a relabelled smooth function is relabelled by
the inverse permutation on its coordinate indices. -/
theorem ginibreEuclideanGradient_comp_permute {n : ℕ}
    (σ : ParticlePermutation n) (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) (z : Configuration n) :
    ginibreEuclideanGradient (fun y => f (permute σ y)) z =
      WithLp.toLp 2 (fun k : Fin n × Fin 2 =>
        ginibreEuclideanGradient f (permute σ z) (σ.symm k.1, k.2)) := by
  apply PiLp.ext
  intro k
  rw [ginibreEuclideanGradient_coordinate, ginibreEuclideanGradient_coordinate]
  let P : Configuration n →L[ℝ] Configuration n :=
    (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin n => ℂ) σ.symm).toContinuousLinearMap
  have hP (y : Configuration n) : P y = permute σ y := by
    funext i
    simp [P, ContinuousLinearEquiv.piCongrLeft, LinearEquiv.piCongrLeft,
      Equiv.piCongrLeft_apply, permute]
  have hcomp : (fun y => f (permute σ y)) = f ∘ P := by
    funext y
    exact congrArg f (hP y).symm
  rw [hcomp]
  have hder := fderiv_comp (x := z) (f := P) (g := f)
    (hf.differentiable (by simp)).differentiableAt P.differentiableAt
  rw [hder]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply]
  have hPder : fderiv ℝ P z = P := (P.hasFDerivAt).fderiv
  rw [hPder, hP z]
  by_cases hk : k.2 = 0
  · simp only [hk, if_pos, ginibreCoordinateDirection]
    rw [show P (realCoordinateDirection k.1) =
      realCoordinateDirection (σ.symm k.1) by rw [hP, permute_realCoordinateDirection]]
  · simp only [hk, if_neg, ginibreCoordinateDirection]
    simp only [if_false]
    rw [show P (imaginaryCoordinateDirection k.1) =
      imaginaryCoordinateDirection (σ.symm k.1) by rw [hP, permute_imaginaryCoordinateDirection]]

end
end GinibrePoincare
