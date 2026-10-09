module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevCoreTransport
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

@[expose] public section

/-! # Full actual Gaussian matrix weak-Sobolev completion through entry coordinates

The positive-density theorem first places an ordinary weak entry-gradient pair
in the closure of compact smooth entry-coordinate pairs. Gaussian density
transport then maps this closure into the actual matrix H¹ completion, with
real coordinate indices reindexed explicitly. Applying the matrix closure LSI
provides both entropy integrability and the sharp energy inequality.
The compact-test derivative equations in the hypotheses use ordinary volume;
the L² value and gradient norms use the Gaussian measure.
-/
open MeasureTheory Matrix
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem matrixEntry_full_weak_pair_mem_H1Completion {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n)
    (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
    (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 (matrixEntryGaussianMeasure e))
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    (matrixEntryL2ToMatrix hn e u,
      fun i => matrixEntryL2ToMatrix hn e
        ((configurationGradientComponent m ((matrixEntryRealIndexEquiv e).symm i)).compLpL
          2 (matrixEntryGaussianMeasure e) g)) ∈ matrixGaussianH1Completion n := by
  letI := matrixEntryGaussianMeasure_isProbability hn e
  obtain ⟨c, hc, hbound⟩ := matrixEntryGaussianMeasure_le_finite_smul_volume e
  exact matrixEntry_core_closure_transport hn e _
    (positive_density_full_weak_pair_mem_closure m (matrixEntryGaussianMeasure e)
      (matrixEntryGaussianDensityReal e) (matrixEntryGaussianDensityReal_continuous e)
      (matrixEntryGaussianDensityReal_pos hn e) (matrixEntryGaussianMeasure_eq_real_density e)
      c hc hbound u g hweak)

/-- The sharp actual Gaussian matrix inequality holds for every ordinary weak
entry-gradient pair, through its actual closed graph and with entropy integrability. -/
theorem matrixEntry_full_weak_pair_lsi {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n)
    (u : Lp ℝ 2 (matrixEntryGaussianMeasure e))
    (g : Lp (EuclideanSpace ℝ (Fin m × Fin 2)) 2 (matrixEntryGaussianMeasure e))
    (hweak : ∀ i : Fin m × Fin 2, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g x i * θ x) = -(∫ x, u x * fderiv ℝ θ x (ginibreCoordinateDirection i))) :
    let q := (matrixEntryL2ToMatrix hn e u,
      fun i => matrixEntryL2ToMatrix hn e
        ((configurationGradientComponent m ((matrixEntryRealIndexEquiv e).symm i)).compLpL
          2 (matrixEntryGaussianMeasure e) g))
    Integrable (fun A => q.1 A ^ 2 * Real.log (q.1 A ^ 2)) (matrixGaussianMeasure n) ∧
      squareEntropy (matrixGaussianMeasure n) q.1 ≤
        (1 / (n : ℝ)) * matrixGaussianSobolevEnergy n q :=
  matrixGaussianH1Completion_lsi n hn _ (matrixEntry_full_weak_pair_mem_H1Completion hn e u g hweak)

end
end GinibrePoincare
