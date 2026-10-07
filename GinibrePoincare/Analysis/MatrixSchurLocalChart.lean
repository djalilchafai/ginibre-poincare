module

public import GinibrePoincare.Analysis.MatrixSchurLinearCoordinates
public import GinibrePoincare.Analysis.MatrixSchurChartDerivative
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

@[expose] public section

open Matrix NormedSpace
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

def schurCoordinateChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p : SchurCoordinates n) : Matrix (Fin n) (Fin n) ℂ :=
  schurAmbientChart T (schurCoordinateEmbedding n p)

@[simp] theorem schurCoordinateChart_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    schurCoordinateChart T 0 = T := by
  simp [schurCoordinateChart, schurAmbientChart, exp_zero]

theorem schurCoordinateChart_hasStrictFDerivAt {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    HasStrictFDerivAt (schurCoordinateChart T) (schurCoordinateTangentCLM T) 0 := by
  let M := Matrix (Fin n) (Fin n) ℂ
  have hfst : HasStrictFDerivAt (Prod.fst : M × M → M)
      (ContinuousLinearMap.fst ℝ M M) (0, 0) := hasStrictFDerivAt_fst
  have hsnd : HasStrictFDerivAt (Prod.snd : M × M → M)
      (ContinuousLinearMap.snd ℝ M M) (0, 0) := hasStrictFDerivAt_snd
  have hexp : HasStrictFDerivAt (exp : M → M) (1 : M →L[ℝ] M) 0 :=
    hasStrictFDerivAt_exp_zero
  have hL := hexp.comp ((0, 0) : M × M) hfst
  have hx : (-Prod.fst) ((0, 0) : M × M) = 0 := by simp
  rw [← hx] at hexp
  have hR := hexp.comp ((0, 0) : M × M) hfst.neg
  have hM := (hasStrictFDerivAt_const T ((0, 0) : M × M)).add hsnd
  have hd := (hL.mul' hM).mul' hR
  have hz : schurCoordinateEmbedding n 0 = ((0, 0) : M × M) := by
    rw [map_zero]
    rfl
  have ha : DifferentiableAt ℝ (schurAmbientChart T) ((0, 0) : M × M) :=
    hd.hasFDerivAt.differentiableAt
  rw [← hz] at hd
  have hc := hd.comp (0 : SchurCoordinates n) (schurCoordinateEmbedding n).hasStrictFDerivAt
  have hs : ∃ D : SchurCoordinates n →L[ℝ] Matrix (Fin n) (Fin n) ℂ,
      HasStrictFDerivAt (schurCoordinateChart T) D 0 := ⟨_, hc⟩
  obtain ⟨D, hD⟩ := hs
  have he : D = schurCoordinateTangentCLM T := by
    have haa : HasFDerivAt (schurAmbientChart T)
        (fderiv ℝ (schurAmbientChart T) (0, 0)) (schurCoordinateEmbedding n 0) := by
      rw [hz]
      exact ha.hasFDerivAt
    have hdf : HasFDerivAt (schurCoordinateChart T)
        ((fderiv ℝ (schurAmbientChart T) (0, 0)).comp (schurCoordinateEmbedding n))
        (0 : SchurCoordinates n) :=
      haa.comp _ (schurCoordinateEmbedding n).hasFDerivAt
    rw [hD.hasFDerivAt.unique hdf]
    apply ContinuousLinearMap.ext
    intro p
    rw [ContinuousLinearMap.comp_apply, schurCoordinateEmbedding_apply,
      schurAmbientChart_fderiv, schurCoordinateTangentCLM_apply]
    rfl
  exact he ▸ hD

def schurLocalChart {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    OpenPartialHomeomorph (SchurCoordinates n) (Matrix (Fin n) (Fin n) ℂ) :=
  HasStrictFDerivAt.toOpenPartialHomeomorph (f' := schurCoordinateTangentEquiv T hT hd)
    (schurCoordinateChart T) (schurCoordinateChart_hasStrictFDerivAt T)

@[simp] theorem schurLocalChart_apply {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i))
    (p : SchurCoordinates n) : schurLocalChart T hT hd p = schurCoordinateChart T p := rfl

theorem schurLocalChart_zero_mem_source {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    0 ∈ (schurLocalChart T hT hd).source :=
  HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source
    (f' := schurCoordinateTangentEquiv T hT hd) (schurCoordinateChart_hasStrictFDerivAt T)

theorem schurLocalChart_self_mem_target {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (hd : Function.Injective (fun i => T i i)) :
    T ∈ (schurLocalChart T hT hd).target := by
  simpa only [schurLocalChart, schurCoordinateChart_zero] using HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
    (f' := schurCoordinateTangentEquiv T hT hd) (schurCoordinateChart_hasStrictFDerivAt T)

#print axioms schurCoordinateChart_hasStrictFDerivAt
#print axioms schurLocalChart_self_mem_target
end
end GinibrePoincare
