module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialDomain
public import GinibrePoincare.Analysis.MatrixSpectralSobolevMatrixLines

@[expose] public section

/-! # Actual ordinary full weak spectral derivatives across every collision -/
open MeasureTheory Filter Matrix MvPolynomial
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixFullSpectralLift_coordinate_weak_test (n d : ℕ)
    (e : Fin (d + 1) ≃ Fin n × Fin n) (F : Configuration n → ℝ)
    (hF : Differentiable ℝ F)
    (hsym : ∀ σ : Fin n ≃ Fin n, ∀ z, F (z ∘ σ) = F z)
    (k : Fin (d + 1) × Fin 2)
    (hg : LocallyIntegrable (fun z => fderiv ℝ
      (fun x => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e x)))
      z (ginibreCoordinateDirection k)) volume)
    (θ : Configuration (d + 1) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    (∫ z, fderiv ℝ
      (fun x => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e x)))
      z (ginibreCoordinateDirection k) * θ z) =
      -(∫ z, matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e z)) *
        fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
  let p := MvPolynomial.renameEquiv ℂ e.symm (matrixCharacteristicResultant n)
  have hp : p ≠ 0 := by
    intro h
    exact matrixCharacteristicResultant_ne_zero n
      ((MvPolynomial.renameEquiv ℂ e.symm).injective (by simpa [p] using h))
  let G := fun z => matrixFullSymmetricSpectralLift n F (Matrix.of (matrixComplexEntryEquiv e z))
  have hG : Continuous G :=
    (continuous_matrixFullSymmetricSpectralLift n F hF.continuous hsym).comp (by fun_prop)
  have hd (z : Configuration (d + 1)) (hz : eval z p ≠ 0) :
      DifferentiableAt ℝ G z := by
    have he : eval z p =
        (Matrix.of (matrixComplexEntryEquiv e z)).charpoly.resultant
          (Matrix.of (matrixComplexEntryEquiv e z)).charpoly.derivative := by
      rw [← matrixCharacteristicResultant_eval]
      simp [p, MvPolynomial.renameEquiv_apply, MvPolynomial.eval_rename,
        matrixComplexEntryEquiv, Function.comp_def]
    have hs : (Matrix.of (matrixComplexEntryEquiv e z)).charpoly.Separable := by
      rw [he] at hz
      by_contra h
      exact hz (Polynomial.resultant_eq_zero_iff.mpr
        ⟨Or.inl (Matrix.charpoly_monic _).ne_zero, h⟩)
    exact (matrixFullSymmetricSpectralLift_differentiableAt n _ hs F hF hsym).comp z
      (by fun_prop)
  exact polynomial_collision_coordinate_weak_test d p hp G hG hd
    hG.locallyIntegrable k hg θ hθ hc

end
end GinibrePoincare
