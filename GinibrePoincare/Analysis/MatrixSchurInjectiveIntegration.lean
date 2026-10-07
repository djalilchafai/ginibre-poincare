module

public import GinibrePoincare.Analysis.MatrixSchurSortedDomain

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem matrixSchurChart_lintegral_of_injOn {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hinj : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) s)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s, g A =
      ∫⁻ p in s, ENNReal.ofReal (vandermondeWeight (fun i => (T + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) *
          g (matrixSchurFrameChart (matrixSchurExponentialFrame n) T p) := by
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  let E := (schurEntryCoordinatesEquiv n).toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  have hE : MeasurePreserving E := schurEntryCoordinates_volume_preserving n
  have hh := hE.setLIntegral_comp_emb E.measurableEmbedding
    (fun z => g (E.symm z)) (matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s)
  have hset : E '' (matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s) =
      matrixSchurEntryChart T '' s := by
    rw [← Set.image_comp]
    rfl
  simp only [E.symm_apply_apply, hset] at hh
  rw [hh]
  letI : Measure.IsAddHaarMeasure (volume : Measure (SchurCoordinates n)) :=
    Measure.prod.instIsAddHaarMeasure
      (volume : Measure (SchurLowerIndex n → ℂ)) (volume : Measure (SchurUpperIndex n → ℂ))
  have hj : InjOn (matrixSchurEntryChart T) s := by
    intro p hp q hq he
    exact hinj hp hq (E.injective he)
  have hi := lintegral_image_eq_lintegral_abs_det_fderiv_mul
    (volume : Measure (SchurCoordinates n)) hs
    (fun p _ => (matrixSchurEntryChart_hasFDerivAt T p).hasFDerivWithinAt)
    hj (fun z => g (E.symm z))
  simp only [matrixSchurEntryDerivative_abs_det T hT] at hi
  rw [hi]
  apply lintegral_congr
  intro p
  have hp : E.symm (matrixSchurEntryChart T p) =
      matrixSchurFrameChart (matrixSchurExponentialFrame n) T p := E.symm_apply_apply _
  rw [hp]

#print axioms matrixSchurChart_lintegral_of_injOn
end
end GinibrePoincare
