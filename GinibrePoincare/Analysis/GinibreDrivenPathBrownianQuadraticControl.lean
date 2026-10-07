module

public import GinibrePoincare.Analysis.GinibreStochasticConfigurationHessianSum
public import GinibrePoincare.Analysis.FiniteDimensionalItoQuadraticControl
public import GinibrePoincare.Analysis.FiniteDimensionalItoUniformChain
public import GinibrePoincare.Analysis.FiniteDimensionalItoActualPathRemainder

@[expose] public section

/-! Actual Volterra increments are controlled by actual Brownian coordinate quadratic sums. -/
open Set MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

theorem ginibreDrivenPath_brownian_quadratic_control {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (ω : Ω)
    (X : ℝ≥0 → Configuration n) (b : ℝ → Configuration n) (T : ℝ≥0)
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ s ∈ Icc (0 : ℝ) T, ‖b s‖ ≤ M)
    (hX : ∀ t ∈ Icc 0 T, X t = X 0 +
      (ginibreConfigurationBrownianNoise n B α ω t-ginibreConfigurationBrownianNoise n B α ω 0)+
      ∫ s in (0 : ℝ)..(t : ℝ), b s) (k : ℕ) :
    itoActualPathQuadraticSum X T k ≤
      2*ginibreConfigurationBrownianCoordinateQuadraticSum n B α T k ω+
        2*(M*((T : ℝ)/((k : ℝ)+1)))*(M*(T : ℝ)) := by
  classical
  let a := fun i : Fin (k+1) =>
    ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k (i.val+1))-
      ginibreConfigurationBrownianNoise n B α ω (ginibreUniformBrownianTime T k i)
  let d := fun i : Fin (k+1) => itoUniformDriftIncrement b T k i
  have hi (i : Fin (k+1)) := itoVolterra_uniform_increment X
    (fun t => ginibreConfigurationBrownianNoise n B α ω t) b T hb hX k i
  have hq := itoConfigurationQuadraticSum_le Finset.univ a d
    (M*((T : ℝ)/((k : ℝ)+1)))
    (fun i hi => itoUniformDriftIncrement_norm_le b T k M hbound i)
  have hv := itoUniformDriftIncrement_variation_le b T k M hbound
  have hm : 0 ≤ 2*(M*((T : ℝ)/((k : ℝ)+1))) := by positivity
  unfold itoActualPathQuadraticSum
  simp_rw [hi]
  calc
    _ ≤ 2*(∑ p : Fin n × Fin 2, ∑ i : Fin (k+1),
        (configurationEuclideanLinearEquiv n (a i) p)^2)+
        2*(M*((T : ℝ)/((k : ℝ)+1)))*(∑ i : Fin (k+1), ‖d i‖) := hq
    _ ≤ _ := add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hv hm)
end
end GinibrePoincare
