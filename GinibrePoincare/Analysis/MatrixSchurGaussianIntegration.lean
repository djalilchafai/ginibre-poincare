module

public import GinibrePoincare.Analysis.MatrixSchurEntryVolume

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

/-- Local Schur change of variables in the original matrix-entry Lebesgue measure. -/
theorem matrixSchurChart_lintegral {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
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
  have hi := matrixSchurEntryChart_lintegral T hT hd s hs hsub (fun z => g (E.symm z))
  rw [hi]
  apply lintegral_congr
  intro p
  have hp : E.symm (matrixSchurEntryChart T p) =
      matrixSchurFrameChart (matrixSchurExponentialFrame n) T p := E.symm_apply_apply _
  rw [hp]

/-- The diagonal Gaussian, strict-upper Gaussian, Vandermonde, and angular factor
appear together in an actual local matrix-volume integral. -/
theorem matrixSchurChart_gaussianDensity_lintegral {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s,
        matrixGaussianDensity n A * g A =
      ∫⁻ p in s, ENNReal.ofReal (vandermondeWeight (fun i => (T + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) *
        ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n) *
          Real.exp (-(n : ℝ) * ∑ i, Complex.normSq ((T + schurUpperCombination p.2) i i)) *
          Real.exp (-(n : ℝ) * matrixHSNormSq
            ((T + schurUpperCombination p.2) - Matrix.diagonal fun i => (T + schurUpperCombination p.2) i i))) *
          g (matrixSchurFrameChart (matrixSchurExponentialFrame n) T p) := by
  rw [matrixSchurChart_lintegral T hT hd s hs hsub]
  apply lintegral_congr
  intro p
  rw [matrixSchurFrameChart, matrixGaussianDensity_unitary_schur n _ _
    (matrixSchurExponentialFrame_unitary n p.1)]
  exact (mul_assoc _ _ _).symm

/-- The local chart integral uses the actual Gaussian matrix probability measure. -/
theorem matrixGaussianMeasure_schurChart_density {n : ℕ} (hn : 0 < n)
    (T : Matrix (Fin n) (Fin n) ℂ) (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i))
    (s : Set (SchurCoordinates n)) (hs : MeasurableSet s)
    (hsub : s ⊆ (schurLocalChart T hT hd).source)
    (g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞) :
    ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s,
        g A ∂matrixGaussianMeasure n =
      ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) T '' s,
        matrixGaussianDensity n A * g A := by
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hi : InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) T) s := by
    rw [matrixSchurExponentialChart_eq]
    exact (schurLocalChart T hT hd).injOn.mono hsub
  have himage := hs.image_of_continuousOn_injOn
    (matrixSchurExponentialChart_differentiable T).continuous.continuousOn hi
  have hm : Measurable (matrixGaussianDensity n) := by
    unfold matrixGaussianDensity
    simp_rw [matrixHSNormSq_eq_sum]
    fun_prop
  rw [matrixGaussianMeasure_eq_withDensity hn]
  exact setLIntegral_withDensity_eq_setLIntegral_mul_non_measurable
    volume hm g himage (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)

#print axioms matrixSchurChart_gaussianDensity_lintegral
#print axioms matrixSchurChart_lintegral
#print axioms matrixGaussianMeasure_schurChart_density
end
end GinibrePoincare
