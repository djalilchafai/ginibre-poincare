module

public import GinibrePoincare.Analysis.MatrixSchurInjectiveIntegration
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

@[expose] public section

open Matrix NormedSpace MeasureTheory
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem matrixSchurExponentialFrame_fderiv_zero (n : ℕ) :
    fderiv ℝ (matrixSchurExponentialFrame n) 0 = schurSkewCLM n := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have he : HasFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 := hasFDerivAt_exp_zero
  have hz : schurSkewCLM n 0 = 0 := map_zero _
  rw [← hz] at he
  have hc := he.comp (0 : SchurLowerIndex n → ℂ) (schurSkewCLM n).hasFDerivAt
  have hf : matrixSchurExponentialFrame n = exp ∘ ⇑(schurSkewCLM n) := by
    funext x
    rw [Function.comp_apply, schurSkewCLM_apply]
    rfl
  rw [hf, hc.fderiv]
  rfl

theorem matrixSchurAngularDensity_zero (n : ℕ) : matrixSchurAngularDensity n 0 = 1 := by
  have hQ : matrixSchurExponentialFrame n 0 = 1 := by
    simp [matrixSchurExponentialFrame, ← schurSkewCLM_apply, exp_zero]
  have hJ : (matrixLowerRead n).comp (matrixUnitaryConnection (matrixSchurExponentialFrame n 0)
      (fderiv ℝ (matrixSchurExponentialFrame n) 0)) =
      ContinuousLinearMap.id ℝ (SchurLowerIndex n → ℂ) := by
    apply ContinuousLinearMap.ext
    intro x
    rw [ContinuousLinearMap.comp_apply, matrixUnitaryConnection_apply, hQ,
      Matrix.conjTranspose_one, Matrix.one_mul, matrixSchurExponentialFrame_fderiv_zero,
      schurSkewCLM_apply, matrixLowerRead_skew]
    rfl
  rw [matrixSchurAngularDensity, hJ]
  simp

theorem measurable_matrixSchurAngularDensity (n : ℕ) :
    Measurable (matrixSchurAngularDensity n) := by
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hQ : Measurable (matrixSchurExponentialFrame n) :=
    (matrixSchurExponentialFrame_differentiable n).continuous.measurable
  have hD : Measurable (fderiv ℝ (matrixSchurExponentialFrame n)) :=
    measurable_fderiv ℝ _
  have hW : Measurable (fun x => matrixUnitaryConnection (matrixSchurExponentialFrame n x)
      (fderiv ℝ (matrixSchurExponentialFrame n) x)) := by
    unfold matrixUnitaryConnection
    fun_prop
  have hJ : Measurable (fun x => (matrixLowerRead n).comp
      (matrixUnitaryConnection (matrixSchurExponentialFrame n x)
        (fderiv ℝ (matrixSchurExponentialFrame n) x))) := by fun_prop
  exact continuous_abs.measurable.comp (ContinuousLinearMap.continuous_det.measurable.comp hJ)

#print axioms measurable_matrixSchurAngularDensity
#print axioms matrixSchurAngularDensity_zero
end
end GinibrePoincare
