module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityConfigurationCutoff
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityDensityEquation
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityWeightedData

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibreLocalRegularity_weighted_resolvent_density_cutoff_gradient
    (n : ℕ) (hn : 0 < n) (ℓ : ℝ) (u f : Configuration n → ℝ)
    (hu : MemLp u 2 (ginibreMeasure n)) (hf : MemLp f 2 (ginibreMeasure n))
    (heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, ginibreLebesgueDensityReal n z*u z*ginibrePregenerator n θ z) =
        (∫ z, ginibreLebesgueDensityReal n z*(ℓ*u z-f z)*θ z))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | CollisionFree z})
    (η : Configuration n → ℝ) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η) (hηK : tsupport η ⊆ K) :
    ∃ g : (Fin n × Fin 2) → Configuration n → ℝ,
      (∀ k, MemLp (g k) 2 (volume : Measure (Configuration n))) ∧
      ∀ k (θ : Configuration n → ℝ), ContDiff ℝ ∞ θ → HasCompactSupport θ →
        (∫ z, θ z*g k z) = -(∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k)*
          (η z*(ginibreLebesgueDensityReal n z*u z))) := by
  obtain ⟨hw,hH,hF⟩ := ginibreLocalRegularity_density_resolvent_data_memLp n hn ℓ u f hu hf K hK hs
  have hF' (k : Fin n × Fin 2) : MemLp
      (fun z => u z*fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)) 2 (volume.restrict K) := by
    have he : (fun z => u z*fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)) =
        (fun z => fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)*u z) := by
      funext z
      ring
    rw [he]
    exact hF _
  apply ginibreLocalRegularity_configuration_cutoff_exists_weak_derivatives n K hK.measurableSet
    (fun z => ginibreLebesgueDensityReal n z*u z)
    (fun z => (n : ℝ)*ginibreLebesgueDensityReal n z*(ℓ*u z-f z))
    (fun k z => u z*fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k))
    hw hH hF' η hη hc hηK
  intro θ hθ hθc hθK
  exact ginibreLocalRegularity_density_resolvent_elliptic_equation n hn ℓ u f hu heq θ hθ hθc (hθK.trans hs)

#print axioms ginibreLocalRegularity_weighted_resolvent_density_cutoff_gradient
end
end GinibrePoincare
