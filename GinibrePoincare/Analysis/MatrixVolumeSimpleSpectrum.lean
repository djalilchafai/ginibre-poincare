module

public import GinibrePoincare.Analysis.MatrixSimpleSpectrum
public import GinibrePoincare.Analysis.MatrixSchurEntryVolume

@[expose] public section

open Matrix MeasureTheory Filter
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem matrixVolume_polynomial_ne_zero_ae {n : ℕ}
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ≠ 0) :
    ∀ᵐ G ∂(volume : Measure (Fin n → Fin n → ℂ)),
      MvPolynomial.eval (fun ij => G ij.1 ij.2) p ≠ 0 :=
  (matrixVolume_uncurry_preserving n).quasiMeasurePreserving.ae
    (complexMvPolynomial_eval_ne_zero_ae (volume : Measure ℂ) p hp)

theorem matrixVolume_charpoly_separable_ae (n : ℕ) :
    ∀ᵐ G ∂(volume : Measure (Fin n → Fin n → ℂ)), (Matrix.of G).charpoly.Separable := by
  filter_upwards [matrixVolume_polynomial_ne_zero_ae
    (matrixCharacteristicResultant n) (matrixCharacteristicResultant_ne_zero n)] with G hG
  rw [matrixCharacteristicResultant_eval] at hG
  by_contra hs
  apply hG
  exact Polynomial.resultant_eq_zero_iff.mpr
    ⟨Or.inl (Matrix.of G).charpoly_monic.ne_zero, hs⟩

#print axioms matrixVolume_charpoly_separable_ae
end
end GinibrePoincare
