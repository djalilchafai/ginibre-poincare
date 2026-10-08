module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryRadialLSI
public import GinibrePoincare.Analysis.AlternativeBakryEmeryRadialProductAssembly
public import GinibrePoincare.Analysis.StrongConvexRadialProductLipschitzLSI
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Concrete tensorization of the actual single-radius Bakry–Émery bounds. -/
theorem bakryEmery_radiusProduct_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0}
    (hLip : LipschitzWith K f) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ r, |f r| ≤ C) :
    squareEntropy (potentialRadiusProduct n V) f ≤ (2/((n:ℝ)*ρ)) *
      ∫ r, directionalEnergy (fun i : Fin n => Pi.single i 1) f r ∂potentialRadiusProduct n V := by
  apply bakryEmery_radiusProduct_lsi_of_factor_lsi n hn ρ hρ V hV hrot hc _ f hf hLip C hC hb
  intro i g hg L hgLip D hD hgBound
  exact bakryEmery_kostlan_radius_bounded_lsi n i.val hn ρ hρ V hV hrot hc g hg hgLip D
    (by intro r; simpa only [Real.norm_eq_abs] using hgBound r)

/-- The independent Bakry–Émery product route extends to bounded Lipschitz
profiles by actual Haar mollification and radial density absolute continuity. -/
theorem bakryEmery_radiusProduct_lsi_lipschitz (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : (Fin n → ℝ) → ℝ) {K : ℝ≥0} (hf : LipschitzWith K f)
    (C : ℝ) (hb : ∀ r, |f r| ≤ C) :
    squareEntropy (potentialRadiusProduct n V) f ≤ (2 / ((n : ℝ) * ρ)) *
      ∫ r, directionalEnergy (fun i : Fin n => Pi.single i 1) f r ∂potentialRadiusProduct n V := by
  have hi (i : Fin n) := rhoConvexPotential_radial_density_integrable n i.val hn ρ hρ hV hrot hc
  letI (i : Fin n) : IsProbabilityMeasure ((potentialSquaredRadiusLaw n i.val V).map Real.sqrt) := by
    rw [← radialConfinementProbabilityDensity_eq_sqrt_map n i.val V hV.continuous (hi i)]
    exact radialConfinementProbabilityDensity_isProbability n i.val _
      (hV.continuous.comp Complex.continuous_ofReal) (hi i)
  letI : IsProbabilityMeasure (potentialRadiusProduct n V) := by
    unfold potentialRadiusProduct
    infer_instance
  apply boundedLipschitz_lsi_of_C1 volume (potentialRadiusProduct n V)
    (rhoConvex_radiusProduct_absolutelyContinuous n hn ρ hρ hV hrot hc)
    (fun i : Fin n => Pi.single i 1) (2 / ((n : ℝ) * ρ)) _ f hf C
    (by intro r; simpa only [Real.norm_eq_abs] using hb r)
  intro g hg L hgL D hgD
  have hD : 0 ≤ D := (norm_nonneg (g 0)).trans (hgD 0)
  exact bakryEmery_radiusProduct_lsi n hn ρ hρ hV hrot hc g hg hgL D hD
    (by intro r; simpa only [Real.norm_eq_abs] using hgD r)

#print axioms bakryEmery_radiusProduct_lsi
#print axioms bakryEmery_radiusProduct_lsi_lipschitz
end
end GinibrePoincare
