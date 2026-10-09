module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularity

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 500000

theorem ginibreLocalRegularity_compact_adjoint_density
    (n : ℕ) (hn : 0 < n) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        (∫ z, f z*θ z ∂ginibreMeasure n)) :
    ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(1*u z-f z)*θ z) := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  intro θ hθ hc hs
  have hθL : MemLp θ 2 (ginibreMeasure n) := hθ.continuous.memLp_of_hasCompactSupport hc
  have hui : Integrable (fun z => ginibreLebesgueDensityReal n z*(u z*θ z)) volume :=
    (integrable_ginibre_iff_density hn (fun z => u z*θ z)).mp (hu.integrable_mul hθL)
  have hfi : Integrable (fun z => ginibreLebesgueDensityReal n z*(f z*θ z)) volume :=
    (integrable_ginibre_iff_density hn (fun z => f z*θ z)).mp (hf.integrable_mul hθL)
  have he := heq θ hθ hc hs
  simp_rw [integral_ginibreMeasure_eq_density_volume hn] at he
  have hm0 : (ginibreNormalizingMass n).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(ginibreMassEvaluation n hn).1.ne', (ginibreMassEvaluation n hn).2.ne⟩
  have he' := congrArg (fun a : ℝ => (ginibreNormalizingMass n).toReal*a) he
  simp only [mul_sub,← mul_assoc, mul_inv_cancel₀ hm0, one_mul] at he'
  have hright : (∫ z, ginibreLebesgueDensityReal n z*(1*u z-f z)*θ z) =
      (∫ z, ginibreLebesgueDensityReal n z*(u z*θ z))-
      (∫ z, ginibreLebesgueDensityReal n z*(f z*θ z)) := by
    calc
      _ = ∫ z, ginibreLebesgueDensityReal n z*(u z*θ z)-ginibreLebesgueDensityReal n z*(f z*θ z) := by
        apply integral_congr_ae
        exact ae_of_all volume fun z => by dsimp only; ring
      _ = _ := integral_sub hui hfi
  simp only [← mul_assoc] at hright
  rw [hright]
  linear_combination -he'

/-- The literal probabilistic adjoint resolvent equation directly supplies
an actual measurable local H¹ gradient. -/
theorem ginibreTransitionAnalytic_compact_adjoint_exists_local_gradient
    (n : ℕ) (hn : 0 < n) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, u z*θ z ∂ginibreMeasure n)-(∫ z, u z*ginibrePregenerator n θ z ∂ginibreMeasure n) =
        (∫ z, f z*θ z ∂ginibreMeasure n)) :
    ∃ g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2), Measurable g ∧
      (∀ K : Set (Configuration n), IsCompact K → K ⊆ {z | CollisionFree z} →
        MemLp g 2 (volume.restrict K)) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        tsupport θ ⊆ {z | CollisionFree z} →
        (∫ z, θ z*g z k) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*u z) :=
  ginibreTransitionAnalytic_weighted_resolvent_exists_local_gradient n hn 1 u f hu hf
    (ginibreLocalRegularity_compact_adjoint_density n hn u f hu hf heq)

#print axioms ginibreTransitionAnalytic_compact_adjoint_exists_local_gradient
end
end GinibrePoincare
