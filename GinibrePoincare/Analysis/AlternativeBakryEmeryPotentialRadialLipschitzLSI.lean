module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryPotentialRadialLSI
public import GinibrePoincare.Analysis.StrongConvexPotentialRadialLipschitzLSI
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped ContDiff NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The independent Bakry–Émery radial LSI for all bounded symmetric Lipschitz magnitude profiles,
under the genuine interacting nonquadratic law, with the actual a.e. gradient. -/
theorem bakryEmery_potential_radial_lsi_lipschitz (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (F : (Fin n → ℝ) → ℝ) (hs : IsSymmetricRadiusTest n F)
    {K : ℝ≥0} (hF : LipschitzWith K F) (C : ℝ) (hb : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V (fun z => F (magnitudeVector z)) := by
  have hfin := rhoConvex_potentialPartition_lt_top n hn ρ hρ hV hrot hc
  rw [potential_magnitude_entropy_eq_radiusProduct n hn hV.continuous hrot hfin F hF.continuous hs C hb,
    rhoConvex_potential_magnitude_gradient_energy_lipschitz n hn ρ hρ hV hrot hc F hs hF]
  exact bakryEmery_radiusProduct_lsi_lipschitz n hn ρ hρ hV hrot hc F hF C hb

/-- The paper's literal bounded Lipschitz radial observable formulation. The
existential radial witness carries no regularity hypothesis. -/
theorem bakryEmery_potential_bounded_lipschitz_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : Configuration n → ℝ) (hs : IsSymmetric f)
    {K : ℝ≥0} (hf : LipschitzWith K f) (C : ℝ) (hb : ∀ z, |f z| ≤ C)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    squareEntropy (potentialMeasure n V) f ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V f := by
  have hemb : Isometry (fun r : Fin n → ℝ => fun i => (r i : ℂ)) :=
    isometry_iff_dist_eq.mpr (by
      intro r s
      simp only [dist_pi_def, Complex.isometry_ofReal.nndist_eq])
  have hp : LipschitzWith K (magnitudeProfile f) := by
    change LipschitzWith K (f ∘ (fun r : Fin n → ℝ => fun i => (r i : ℂ)))
    simpa only [mul_one] using hf.comp hemb.lipschitzWith
  have he : f = (fun z => magnitudeProfile f (magnitudeVector z)) := by
    funext z
    exact radial_eq_magnitudeProfile f hr z
  have ht := bakryEmery_potential_radial_lsi_lipschitz n hn ρ hρ hV hrot hc
    (magnitudeProfile f) (magnitudeProfile_symmetric f hs) hp C (fun r => hb _)
  rwa [← he] at ht

#print axioms bakryEmery_potential_radial_lsi_lipschitz
#print axioms bakryEmery_potential_bounded_lipschitz_radial_lsi
end
end GinibrePoincare
