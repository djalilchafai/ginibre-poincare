module

public import GinibrePoincare.Analysis.MatrixGaussianUnitaryInvariant
public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

@[expose] public section

open Matrix MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixUnitaryRealMap_abs_det {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |(matrixUnitaryRealMap U).toLinearMap.det| = 1 := by
  have hn : ‖(matrixUnitaryEuclideanMap U).det‖ = 1 := by
    rw [← LinearMap.normDet_eq_norm_det]
    exact (matrixUnitaryEuclideanIsometry U hU).normDet_eq_one
  have hd : (matrixUnitaryEuclideanMap U).det = (matrixUnitaryRealMap U).toLinearMap.det := by
    exact LinearMap.det_conj (matrixUnitaryRealMap U).toLinearMap
      (WithLp.linearEquiv 2 ℝ (MatrixRealIndex n → ℝ)).symm
  rw [hd, Real.norm_eq_abs] at hn
  exact hn

theorem matrixUnitaryConjugation_abs_det {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    |(matrixUnitaryConjugation U).toLinearMap.det| = 1 := by
  have hd : (matrixUnitaryConjugation U).toLinearMap.det = (matrixUnitaryRealMap U).toLinearMap.det := by
    exact LinearMap.det_conj (matrixUnitaryRealMap U).toLinearMap
      (matrixRealCoordinates n).toLinearEquiv
  rw [hd]
  exact matrixUnitaryRealMap_abs_det U hU

theorem matrixUnitaryConjugation_volume_map {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (volume : Measure (Fin n → Fin n → ℂ)).map (matrixUnitaryConjugation U) = volume := by
  letI : Measure.IsAddHaarMeasure (volume : Measure (Fin n → Fin n → ℂ)) :=
    Measure.pi.isAddHaarMeasure _
  have ha := matrixUnitaryConjugation_abs_det U hU
  have hd : (matrixUnitaryConjugation U).toLinearMap.det ≠ 0 := by
    intro hh
    rw [hh, abs_zero] at ha
    norm_num at ha
  have hm := Measure.map_linearMap_addHaar_eq_smul_addHaar
    (volume : Measure (Fin n → Fin n → ℂ)) hd
  have hm' := hm
  simp only [abs_inv, ha, inv_one, ENNReal.ofReal_one, one_smul] at hm'
  exact hm'

#print axioms matrixUnitaryConjugation_volume_map
#print axioms matrixUnitaryConjugation_abs_det
end
end GinibrePoincare
