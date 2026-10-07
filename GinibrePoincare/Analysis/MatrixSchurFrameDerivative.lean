module

public import GinibrePoincare.Analysis.MatrixSchurMovingJacobian
public import GinibrePoincare.Analysis.MatrixUnitaryDerivative

@[expose] public section

open Matrix Filter
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def matrixUnitaryConnection {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ) :
    (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (((ContinuousLinearMap.mul ℂ (Matrix (Fin n) (Fin n) ℂ)) Qᴴ).restrictScalars ℝ).comp D

theorem matrixUnitaryConnection_apply {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (v : SchurLowerIndex n → ℂ) : matrixUnitaryConnection Q D v = Qᴴ * D v := rfl

def matrixSchurFrameChart {n : ℕ} (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (p : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  Q p.1 * (T + schurUpperCombination p.2) * (Q p.1)ᴴ

theorem matrixSchurFrameChart_normalized_fderiv {n : ℕ}
    (Q : (SchurLowerIndex n → ℂ) → Matrix (Fin n) (Fin n) ℂ)
    (T : Matrix (Fin n) (Fin n) ℂ) (x v : SchurLowerIndex n → ℂ)
    (y h : SchurUpperIndex n → ℂ)
    (D : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ)
    (hQ : HasFDerivAt Q D x) (hunit : ∀ᶠ z in 𝓝 x, Q z ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    (Q x)ᴴ * fderiv ℝ (matrixSchurFrameChart Q T) (x, y) (v, h) * Q x =
      schurMovingTangent (T + schurUpperCombination y) (matrixUnitaryConnection (Q x) D) (v, h) := by
  let X := SchurLowerIndex n → ℂ
  let Y := SchurUpperIndex n → ℂ
  let M := Matrix (Fin n) (Fin n) ℂ
  let F := ContinuousLinearMap.fst ℝ X Y
  let S := ContinuousLinearMap.snd ℝ X Y
  have hq := hQ.comp ((x, y) : X × Y) F.hasFDerivAt
  have hu := ((schurUpperCLM n).restrictScalars ℝ).hasFDerivAt.comp ((x, y) : X × Y) S.hasFDerivAt
  have ht := (hasFDerivAt_const (𝕜 := ℝ) T ((x, y) : X × Y)).add hu
  have ha := (schurConjTransposeCLM n).hasFDerivAt.comp ((x, y) : X × Y) hq
  have hp := (hq.mul' ht).mul' ha
  have hf : (matrixSchurFrameChart Q T : X × Y → M) =
      (Q ∘ ⇑F * ((fun _ => T) + ⇑((schurUpperCLM n).restrictScalars ℝ) ∘ ⇑S) *
        ⇑(schurConjTransposeCLM n) ∘ Q ∘ ⇑F) := by
    funext p
    change Q p.1 * (T + schurUpperCombination p.2) * (Q p.1)ᴴ =
      Q p.1 * (T + schurUpperCLM n p.2) * (Q p.1)ᴴ
    rw [schurUpperCLM_apply]
  have hpf := hp.fderiv
  rw [hf]
  rw [hpf]
  have hux : Q x ∈ Matrix.unitaryGroup (Fin n) ℂ := hunit.self_of_nhds
  have h1 : (Q x)ᴴ * Q x = 1 := Matrix.mem_unitaryGroup_iff'.mp hux
  have h2 : Q x * (Q x)ᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hux
  have hw := matrixUnitary_left_derivative_skew hQ hunit v
  rw [schurMovingTangent_apply, matrixUnitaryConnection_apply]
  have hh : (D v)ᴴ * Q x = -((Q x)ᴴ * D v) := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] using hw
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply,
    ContinuousLinearMap.coe_restrictScalars', Function.comp_apply, Pi.mul_apply, Pi.add_apply,
    F, S, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', zero_add,
    schurConjTransposeCLM, LinearMap.coe_toContinuousLinearMap', schurUpperCLM_apply, smul_eq_mul, op_smul_eq_mul]
  change (Q x)ᴴ *
      ((Q x * (T + schurUpperCombination y)) * (D v)ᴴ +
        (Q x * schurUpperCombination h + D v * (T + schurUpperCombination y)) * (Q x)ᴴ) * Q x =
    ((Q x)ᴴ * D v) * (T + schurUpperCombination y) -
      (T + schurUpperCombination y) * ((Q x)ᴴ * D v) + schurUpperCombination h
  calc
    _ = ((Q x)ᴴ * Q x) * (T + schurUpperCombination y) * (D v)ᴴ * Q x +
        ((Q x)ᴴ * Q x) * schurUpperCombination h * ((Q x)ᴴ * Q x) +
        (Q x)ᴴ * D v * (T + schurUpperCombination y) * ((Q x)ᴴ * Q x) := by noncomm_ring
    _ = (T + schurUpperCombination y) * ((D v)ᴴ * Q x) + schurUpperCombination h +
        ((Q x)ᴴ * D v) * (T + schurUpperCombination y) := by
      rw [h1]
      simp [Matrix.mul_assoc]
    _ = _ := by rw [hh]; noncomm_ring

#print axioms matrixSchurFrameChart_normalized_fderiv
end
end GinibrePoincare
