module

public import GinibrePoincare.Analysis.MatrixSchurCoordinates
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section

open Matrix
open scoped Matrix Matrix.Norms.Operator BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def schurLowerCLM (n : ℕ) : (SchurLowerIndex n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, (ContinuousLinearMap.proj p).smulRight (Matrix.single (schurLowerRow p) (schurLowerCol p) 1)

def schurUpperCLM (n : ℕ) : (SchurUpperIndex n → ℂ) →L[ℂ] Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, (ContinuousLinearMap.proj p).smulRight (Matrix.single p.val.1 p.val.2 1)

theorem schurLowerCLM_apply (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    schurLowerCLM n x = schurLowerCombination x := by
  simp [schurLowerCLM, schurLowerCombination]

theorem schurUpperCLM_apply (n : ℕ) (x : SchurUpperIndex n → ℂ) :
    schurUpperCLM n x = schurUpperCombination x := by
  simp [schurUpperCLM, schurUpperCombination]

def schurConjTransposeCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun r A => by simp [Matrix.conjTranspose_smul] }

def schurSkewCLM (n : ℕ) : (SchurLowerIndex n → ℂ) →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  (schurLowerCLM n).restrictScalars ℝ -
    (schurConjTransposeCLM n).comp ((schurLowerCLM n).restrictScalars ℝ)

theorem schurSkewCLM_apply (n : ℕ) (x : SchurLowerIndex n → ℂ) :
    schurSkewCLM n x = schurSkewCombination x := by
  simp [schurSkewCLM, schurConjTransposeCLM, schurLowerCLM_apply, schurSkewCombination]

def schurCoordinateEmbedding (n : ℕ) : SchurCoordinates n →L[ℝ]
    (Matrix (Fin n) (Fin n) ℂ × Matrix (Fin n) (Fin n) ℂ) :=
  ((schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ _ _)).prod
    (((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _))

theorem schurCoordinateEmbedding_apply (n : ℕ) (p : SchurCoordinates n) :
    schurCoordinateEmbedding n p = (schurSkewCombination p.1, schurUpperCombination p.2) := by
  simp [schurCoordinateEmbedding, schurSkewCLM_apply, schurUpperCLM_apply]

#print axioms schurCoordinateEmbedding_apply

def schurCoordinateTangentCLM {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
  let S : SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (schurSkewCLM n).comp (ContinuousLinearMap.fst ℝ _ _)
  ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)).flip T).comp S -
    ((ContinuousLinearMap.mul ℝ (Matrix (Fin n) (Fin n) ℂ)) T).comp S +
      ((schurUpperCLM n).restrictScalars ℝ).comp (ContinuousLinearMap.snd ℝ _ _)

theorem schurCoordinateTangentCLM_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : schurCoordinateTangentCLM T p = schurCoordinateTangent T p := by
  simp [schurCoordinateTangentCLM, schurCoordinateTangent, schurSkewCLM_apply, schurUpperCLM_apply]

def schurCoordinateTangentEquiv {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    SchurCoordinates n ≃L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
by
  have he : (schurCoordinateTangentCLM T : SchurCoordinates n → Matrix (Fin n) (Fin n) ℂ) =
      schurCoordinateTangent T := funext (schurCoordinateTangentCLM_apply T)
  have hb : Function.Bijective (schurCoordinateTangentCLM T) :=
    he.symm ▸ schurCoordinateTangent_bijective T hT hd
  exact ContinuousLinearEquiv.ofBijective (schurCoordinateTangentCLM T)
    (LinearMap.ker_eq_bot.mpr hb.1) (LinearMap.range_eq_top.mpr hb.2)

#print axioms schurCoordinateTangentEquiv
end
end GinibrePoincare
