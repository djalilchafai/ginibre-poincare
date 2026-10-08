module
public import GinibrePoincare.Analysis.CorrespondenceGUEOrderedLSI
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBoundedLSIClosure
@[expose] public section
open MeasureTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueDoubledOrderedMeasure_boundedC1_square_lsi {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hK : LipschitzWith K f) (C : ℝ) (hC : ∀x, ‖f x‖≤C) :
    squareEntropy (gueDoubledOrderedMeasure n) f ≤
      (2/(n:ℝ))*∫ x, ‖gradient f x‖^2 ∂gueDoubledOrderedMeasure n := by
  letI := gueDoubledOrderedMeasure_probability hn
  let b := stdOrthonormalBasis ℝ (EuclideanSpace ℝ (Fin n×Fin 2))
  have hc : ∀g : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ,
      ContDiff ℝ 1 g → HasCompactSupport g →
      squareEntropy (gueDoubledOrderedMeasure n) g ≤
        (2/(n:ℝ))*∫ x,directionalEnergy b g x ∂gueDoubledOrderedMeasure n := by
    intro g hg hs
    simpa only [bakryEmery_directionalEnergy_orthonormalBasis] using
      gueDoubledOrderedMeasure_square_lsi hn g hg hs
  have h := bakryEmery_boundedC1_lsi_of_compact
    (EuclideanSpace ℝ (Fin n×Fin 2)) (gueDoubledOrderedMeasure n) b _ hc f hf K hK C hC
  simpa only [bakryEmery_directionalEnergy_orthonormalBasis] using h

#print axioms gueDoubledOrderedMeasure_boundedC1_square_lsi
end
end GinibrePoincare
