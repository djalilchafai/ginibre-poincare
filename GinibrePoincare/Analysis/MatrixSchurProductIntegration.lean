module

public import GinibrePoincare.Analysis.MatrixSchurAngularDensity

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set
open scoped Matrix Matrix.Norms.Operator Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option maxRecDepth 10000

/-- An actual product Schur chart separates its angular integral from its spectral and
strict upper integral for every measurable unitary-conjugation-invariant observable. -/
theorem matrixSchur_product_integral (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      ∀ g : Matrix (Fin n) (Fin n) ℂ → ℝ≥0∞, Measurable g →
        (∀ U ∈ Matrix.unitaryGroup (Fin n) ℂ, ∀ A, g (U * A * Uᴴ) = g A) →
        ∫⁻ A in matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ) ''
            (V ×ˢ matrixSchurSortedUpperDomain n), g A =
          (∫⁻ x in V, ENNReal.ofReal (matrixSchurAngularDensity n x)) *
            ∫⁻ y in matrixSchurSortedUpperDomain n,
              ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination y i i)) *
                g (schurUpperCombination y) := by
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  obtain ⟨V, hV, h0, hinj⟩ := matrixSchurSortedDomain_exists_injective n
  refine ⟨V, hV, h0, ?_⟩
  intro g hg hInv
  have hs : MeasurableSet (V ×ˢ matrixSchurSortedUpperDomain n) :=
    hV.measurableSet.prod (measurableSet_matrixSchurSortedUpperDomain n)
  have hi := matrixSchurChart_lintegral_of_injOn (0 : Matrix (Fin n) (Fin n) ℂ)
    (by intros; rfl) (V ×ˢ matrixSchurSortedUpperDomain n) hs hinj g
  rw [hi]
  have hfun : (fun p : SchurCoordinates n =>
      ENNReal.ofReal (vandermondeWeight (fun i => ((0 : Matrix (Fin n) (Fin n) ℂ) + schurUpperCombination p.2) i i) *
        matrixSchurAngularDensity n p.1) *
        g (matrixSchurFrameChart (matrixSchurExponentialFrame n) 0 p)) =
      (fun p => ENNReal.ofReal (matrixSchurAngularDensity n p.1) *
        (ENNReal.ofReal (vandermondeWeight (fun i => schurUpperCombination p.2 i i)) *
          g (schurUpperCombination p.2))) := by
    funext p
    simp only [zero_add, matrixSchurFrameChart]
    rw [hInv _ (matrixSchurExponentialFrame_unitary n p.1),
      ENNReal.ofReal_mul (vandermondeWeight_nonneg _)]
    ac_rfl
  rw [hfun, Measure.volume_eq_prod, ← Measure.prod_restrict]
  have hU : Measurable (schurUpperCombination (n := n)) := by
    have he : (schurUpperCombination (n := n)) = schurUpperCLM n :=
      funext fun y => (schurUpperCLM_apply n y).symm
    rw [he]
    exact (schurUpperCLM n).continuous.measurable
  have hv : Measurable (fun y : SchurUpperIndex n → ℂ =>
      vandermondeWeight (fun i => schurUpperCombination y i i)) := by
    have hd : Measurable (fun y : SchurUpperIndex n → ℂ =>
        fun i : Fin n => schurUpperCombination y i i) := by fun_prop
    exact Complex.continuous_normSq.measurable.comp (continuous_vandermonde.measurable.comp hd)
  exact lintegral_prod_mul
    (ENNReal.measurable_ofReal.comp (measurable_matrixSchurAngularDensity n)).aemeasurable
    ((ENNReal.measurable_ofReal.comp hv).mul (hg.comp hU)).aemeasurable

#print axioms matrixSchur_product_integral
end
end GinibrePoincare
