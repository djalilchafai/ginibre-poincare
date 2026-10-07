module

public import GinibrePoincare.Analysis.GaussianFiniteIndexLSI
public import GinibrePoincare.Analysis.GaussianCurryLaw
public import GinibrePoincare.Analysis.BlockMagnitudeLift

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

abbrev GaussianBlockRealIndex (n : ℕ) := Σ i : Fin n, Σ _j : Fin (i.val + 1), Fin 2

def gaussianBlockCoordinates (n : ℕ) :
    (GaussianBlockRealIndex n → ℝ) ≃L[ℝ] GaussianRadialBlocks n :=
  (gaussianCurryEquiv (Fin n) (fun i => Σ _ : Fin (i.val + 1), Fin 2)).trans
    (ContinuousLinearEquiv.piCongrRight (fun i : Fin n =>
      (gaussianCurryEquiv (Fin (i.val + 1)) (fun _ => Fin 2)).trans
        (ContinuousLinearEquiv.piCongrRight (fun _ : Fin (i.val + 1) =>
          Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm))))

theorem gaussianBlockCoordinates_measurePreserving (n : ℕ) :
    MeasurePreserving (gaussianBlockCoordinates n)
      (Measure.pi (fun _ : GaussianBlockRealIndex n => gaussianReal 0 (realCoordinateVariance n)))
      (gaussianRadialBlockMeasure n) := by
  let v := realCoordinateVariance n
  have hcomplex : MeasurePreserving Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm
      (Measure.pi (fun _ : Fin 2 => gaussianReal 0 v))
      (complexCoordinateGaussianProbability n : Measure ℂ) := by
    refine ⟨Complex.basisOneI.equivFun.toContinuousLinearEquiv.symm.continuous.measurable, ?_⟩
    unfold complexCoordinateGaussianProbability
    simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_pi]
    rfl
  have hinner (i : Fin n) := (measurePreserving_pi _ _ (fun _ : Fin (i.val + 1) => hcomplex)).comp
    (gaussianCurry_measurePreserving (Fin (i.val + 1)) (fun _ => Fin 2) v)
  have h := (measurePreserving_pi _ _ hinner).comp
    (gaussianCurry_measurePreserving (Fin n) (fun i => Σ _ : Fin (i.val + 1), Fin 2) v)
  exact h

theorem gaussianBlockCoordinates_real_direction (n : ℕ) (i : Fin n) (j : Fin (i.val + 1)) :
    gaussianBlockCoordinates n (Pi.single ⟨i, ⟨j, 0⟩⟩ 1) =
      Pi.single i (realCoordinateDirection j) := by
  classical
  funext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [gaussianBlockCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
        LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply,
        realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection]
    · simp [gaussianBlockCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
        LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply, realCoordinateDirection, coordinateDirection, hb]
  · simp [gaussianBlockCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
      LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply, realCoordinateDirection, coordinateDirection, ha]

theorem gaussianBlockCoordinates_imaginary_direction (n : ℕ) (i : Fin n) (j : Fin (i.val + 1)) :
    gaussianBlockCoordinates n (Pi.single ⟨i, ⟨j, 1⟩⟩ 1) =
      Pi.single i (imaginaryCoordinateDirection j) := by
  classical
  funext a b
  by_cases ha : a = i
  · subst a
    by_cases hb : b = j
    · subst b
      simp [gaussianBlockCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
        LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply,
        realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection]
    · simp [gaussianBlockCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
        LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply, imaginaryCoordinateDirection, coordinateDirection, hb]
  · simp [gaussianBlockCoordinates, gaussianCurryEquiv, ContinuousLinearEquiv.piCongrRight,
      LinearEquiv.piCurry, Equiv.piCurry, Sigma.curry, Pi.single_apply, imaginaryCoordinateDirection, coordinateDirection, ha]

theorem gaussianBlockCoordinates_energy (n : ℕ) (H : GaussianRadialBlocks n → ℝ)
    (x : GaussianBlockRealIndex n → ℝ) :
    directionalEnergy (fun i : GaussianBlockRealIndex n => Pi.single i 1)
      (H ∘ gaussianBlockCoordinates n) x =
        blockGradientNormSq H (gaussianBlockCoordinates n x) := by
  unfold directionalEnergy blockGradientNormSq
  rw [ContinuousLinearEquiv.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Fin.sum_univ_two, gaussianBlockCoordinates_real_direction, gaussianBlockCoordinates_imaginary_direction]

/-- The sharp Gaussian block input required by the full radial Ginibre LSI. -/
theorem gaussianBlock_lsi (n : ℕ) (hn : 0 < n) : GaussianBlockLipschitzLSIStatement n := by
  classical
  letI : Nonempty (GaussianBlockRealIndex n) := ⟨⟨⟨0, hn⟩, ⟨⟨0, by omega⟩, 0⟩⟩⟩
  intro H hH hc
  obtain ⟨K, hK⟩ := hH
  let T := gaussianBlockCoordinates n
  have hp := gaussianBlockCoordinates_measurePreserving n
  have he := gaussianFiniteIndex_lsi_compactLipschitz (GaussianBlockRealIndex n)
    (realCoordinateVariance n) (H ∘ T) (hK.comp T.lipschitzWith) (hc.comp_homeomorph T.toHomeomorph)
  have hent : squareEntropy (gaussianRadialBlockMeasure n) H =
      squareEntropy (Measure.pi (fun _ : GaussianBlockRealIndex n => gaussianReal 0 (realCoordinateVariance n))) (H ∘ T) := by
    rw [← hp.map_eq]
    exact squareEntropy_map _ _ T.continuous.measurable.aemeasurable H
      (hK.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hK.continuous).aestronglyMeasurable
  have hm : Measurable (blockGradientNormSq H) := by
    unfold blockGradientNormSq
    apply Finset.measurable_sum
    intro i hi
    apply Finset.measurable_sum
    intro j hj
    exact ((measurable_fderiv_apply_const ℝ H _).pow_const 2).add
      ((measurable_fderiv_apply_const ℝ H _).pow_const 2)
  have hi : (∫ x, blockGradientNormSq H x ∂gaussianRadialBlockMeasure n) =
      ∫ x, directionalEnergy (fun i : GaussianBlockRealIndex n => Pi.single i 1) (H ∘ T) x
        ∂Measure.pi (fun _ : GaussianBlockRealIndex n => gaussianReal 0 (realCoordinateVariance n)) := by
    rw [← hp.map_eq, integral_map T.continuous.measurable.aemeasurable hm.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun x => (gaussianBlockCoordinates_energy n H x).symm))
  have hv : 2 * (realCoordinateVariance n : ℝ) = 1 / (n : ℝ) := by
    simp [realCoordinateVariance, NNReal.coe_inv, NNReal.coe_mul]
    field_simp
  rw [hent, hi, ← hv]
  exact he

end
end GinibrePoincare
