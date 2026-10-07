module

public import GinibrePoincare.Analysis.MatrixGaussianMeasure
public import GinibrePoincare.Analysis.GaussianBlockLSI

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MatrixRealIndex (n : ℕ) := Σ _ : Fin n, Σ _ : Fin n, Fin 2

def matrixRealCoordinates (n : ℕ) :
    (MatrixRealIndex n → ℝ) ≃L[ℝ] (Fin n → Fin n → ℂ) :=
  (gaussianCurryEquiv (Fin n) (fun _ => Σ _ : Fin n, Fin 2)).trans
    (ContinuousLinearEquiv.piCongrRight (fun _ : Fin n =>
      (gaussianCurryEquiv (Fin n) (fun _ => Fin 2)).trans
        (ContinuousLinearEquiv.piCongrRight (fun _ : Fin n =>
          Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm))))

theorem matrixRealCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (matrixRealCoordinates n)
      (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 (realCoordinateVariance n)))
      (matrixGaussianMeasure n) := by
  let v := realCoordinateVariance n
  have hcomplex : MeasurePreserving Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 v))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
    refine ⟨Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.continuous.measurable, ?_⟩
    unfold complexCoordinateGaussianProbability
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi]
    rfl
  have hinner := (measurePreserving_pi _ _ (fun _ : Fin n => hcomplex)).comp
    (gaussianCurry_measurePreserving (Fin n) (fun _ => Fin 2) v)
  exact (measurePreserving_pi _ _ (fun _ : Fin n => hinner)).comp
    (gaussianCurry_measurePreserving (Fin n) (fun _ => Σ _ : Fin n, Fin 2) v)

def matrixRealGradientEnergy (n : ℕ) (F : (Fin n → Fin n → ℂ) → ℝ) :
    (Fin n → Fin n → ℂ) → ℝ :=
  directionalEnergy (fun i : MatrixRealIndex n => matrixRealCoordinates n (Pi.single i 1)) F

theorem matrixRealCoordinates_direction (n : ℕ) (i j : Fin n) (k : Fin 2) :
    matrixRealCoordinates n (Pi.single ⟨i, ⟨j, k⟩⟩ 1) =
      Pi.single i (Pi.single j (if k = 0 then (1 : ℂ) else Complex.I)) := by
  classical
  funext a b
  fin_cases k <;>
    by_cases ha : a = i <;> by_cases hb : b = j <;>
    simp [matrixRealCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
      LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply, ha, hb,
      Complex.basisOneI, Complex.equivRealProdCLM, Complex.equivRealProd]

/-- Sharp LSI for the actual Gaussian matrix ensemble and compactly supported Lipschitz
matrix observables, in its real entry coordinates. -/
theorem matrixGaussian_lsi_compactLipschitz (n : ℕ) (hn : 0 < n)
    (F : (Fin n → Fin n → ℂ) → ℝ) {K : ℝ≥0}
    (hF : LipschitzWith K F) (hc : HasCompactSupport F) :
    squareEntropy (matrixGaussianMeasure n) F ≤
      (1 / (n : ℝ)) * ∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n := by
  classical
  letI : Nonempty (MatrixRealIndex n) := ⟨⟨⟨0, hn⟩, ⟨⟨0, hn⟩, 0⟩⟩⟩
  let T := matrixRealCoordinates n
  have hp := matrixRealCoordinates_measurePreserving n
  have he := gaussianFiniteIndex_lsi_compactLipschitz (MatrixRealIndex n)
    (realCoordinateVariance n) (F ∘ T) (hF.comp T.lipschitzWith)
    (hc.comp_homeomorph T.toHomeomorph)
  have hent : squareEntropy (matrixGaussianMeasure n) F =
      squareEntropy (Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0
        (realCoordinateVariance n))) (F ∘ T) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ T.continuous.measurable.aemeasurable F
      (hF.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hF.continuous).aestronglyMeasurable
  have hm : Measurable (matrixRealGradientEnergy n F) := by
    unfold matrixRealGradientEnergy directionalEnergy
    exact Finset.measurable_sum _ fun i _ => (measurable_fderiv_apply_const ℝ F _).pow_const 2
  have henergy (x : MatrixRealIndex n → ℝ) :
      directionalEnergy (fun i : MatrixRealIndex n => Pi.single i 1) (F ∘ T) x =
        matrixRealGradientEnergy n F (T x) := by
    unfold matrixRealGradientEnergy directionalEnergy
    rw [ContinuousLinearEquiv.comp_right_fderiv]
    rfl
  have hi : (∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n) =
      ∫ x, directionalEnergy (fun i : MatrixRealIndex n => Pi.single i 1) (F ∘ T) x
        ∂Measure.pi (fun _ : MatrixRealIndex n => gaussianReal 0 (realCoordinateVariance n)) := by
    change (∫ A : Fin n → Fin n → ℂ, matrixRealGradientEnergy n F A
      ∂(matrixGaussianMeasure n : Measure (Fin n → Fin n → ℂ))) = _
    rw [← hp.map_eq, integral_map T.continuous.measurable.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => (henergy x).symm)
  have hv : 2 * (realCoordinateVariance n : ℝ) = 1 / (n : ℝ) := by
    simp [realCoordinateVariance, NNReal.coe_inv, NNReal.coe_mul]
    field_simp
  rw [hent, hi, ← hv]
  exact he

#print axioms matrixGaussian_lsi_compactLipschitz
end
end GinibrePoincare
