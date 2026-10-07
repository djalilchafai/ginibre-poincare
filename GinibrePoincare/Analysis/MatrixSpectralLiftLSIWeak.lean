module

public import GinibrePoincare.Analysis.MatrixSpectralLiftEntryLp
public import GinibrePoincare.Analysis.MatrixSpectralSobolevWeakDomain

@[expose] public section

open Matrix MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator ENNReal ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option maxRecDepth 10000

/-- Ordinary volume weak derivatives of actual intrinsic entry representatives
produce the sharp Ginibre matrix-overlap LSI through the proved matrix H1 domain.
This intermediate theorem assumes no inequality or graph-membership conclusion. -/
theorem matrixSpectralLift_ordinary_weak_lsi {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (F : (Fin n → ℂ) → ℝ) (hF : Differentiable ℝ F)
    (hsym : ∀ p : Fin n ≃ Fin n, ∀ z, F (z ∘ p) = F z)
    (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
    (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 (matrixEntryGaussianMeasure e))
    (hu : (u : Configuration m → ℝ) =ᵐ[matrixEntryGaussianMeasure e]
      (fun x => matrixSymmetricLift n F (matrixComplexEntryEquiv e x)))
    (hg : (g : Configuration m → EuclideanSpace ℝ (Fin m × Fin 2)) =ᵐ[matrixEntryGaussianMeasure e]
      matrixEntryIntrinsicSpectralGradient e F)
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    Integrable (fun z => F z ^ 2 * Real.log (F z ^ 2)) (ginibreMeasure n) ∧
      squareEntropy (ginibreMeasure n) F ≤
        (4 / (n : ℝ)) * ∫ A, matrixSpectralOverlapEnergy n F A ∂matrixGaussianMeasure n := by
  let q : MatrixGaussianSobolevPair n := (matrixEntryL2ToMatrix hn e u,
    fun i => matrixEntryL2ToMatrix hn e
      ((configurationGradientComponent m ((matrixEntryRealIndexEquiv e).symm i)).compLpL
        2 (matrixEntryGaussianMeasure e) g))
  have hq : q ∈ matrixGaussianH1Completion n := matrixEntry_full_weak_pair_mem_H1Completion hn e u g hweak
  have hpres := (matrixComplexEntryEquiv_gaussian_preserving hn e).symm (matrixEntryMeasurableEquiv e)
  have hv : (q.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] matrixSymmetricLift n F := by
    filter_upwards [matrixEntryL2ToMatrix_ae hn e u, hpres.quasiMeasurePreserving.ae hu] with A hA hB
    change u ((matrixComplexEntryEquiv e).symm A) =
      matrixSymmetricLift n F (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A)) at hB
    rw [ContinuousLinearEquiv.apply_symm_apply] at hB
    exact hA.trans hB
  have hd : ∀ i, (q.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ (matrixSymmetricLift n F) A (matrixRealCoordinates n (Pi.single i 1))) := by
    intro i
    let j := (matrixEntryRealIndexEquiv e).symm i
    have hc := (configurationGradientComponent m j).coeFn_compLpL g
    filter_upwards [matrixEntryL2ToMatrix_ae hn e ((configurationGradientComponent m j).compLpL
      2 (matrixEntryGaussianMeasure e) g), hpres.quasiMeasurePreserving.ae hc,
      hpres.quasiMeasurePreserving.ae hg] with A hA hB hC
    change ((configurationGradientComponent m j).compLpL 2 (matrixEntryGaussianMeasure e) g)
      ((matrixComplexEntryEquiv e).symm A) = g ((matrixComplexEntryEquiv e).symm A) j at hB
    change g ((matrixComplexEntryEquiv e).symm A) =
      matrixEntryIntrinsicSpectralGradient e F ((matrixComplexEntryEquiv e).symm A) at hC
    rw [hA, hB]
    have hCj := congrArg (fun v : EuclideanSpace ℝ (Fin m × Fin 2) => v j) hC
    rw [hCj]
    change fderiv ℝ (matrixSymmetricLift n F)
      (matrixComplexEntryEquiv e ((matrixComplexEntryEquiv e).symm A))
      (matrixRealCoordinates n (Pi.single (matrixEntryRealIndexEquiv e j) 1)) = _
    rw [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact matrixSpectralLift_H1_lsi hn F hF hsym q hq hv hd

#print axioms matrixSpectralLift_ordinary_weak_lsi
end
end GinibrePoincare
