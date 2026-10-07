module

public import GinibrePoincare.Analysis.StrongConvexRadialGradientTransfer
public import GinibrePoincare.Analysis.StrongConvexPotentialPartition

@[expose] public section

open MeasureTheory
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section

/-- Sharp radial LSI for the actual interacting nonquadratic log gas, obtained
from its actual Kostlan law and the derived contracting Gaussian quantiles. -/
theorem rhoConvex_potential_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (F : (Fin n → ℝ) → ℝ) (hF : ContDiff ℝ 1 F)
    (hs : IsSymmetricRadiusTest n F) {K : ℝ≥0} (hLip : LipschitzWith K F)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ r, |F r| ≤ C) :
    squareEntropy (potentialMeasure n V) (fun z => F (magnitudeVector z)) ≤
      (2 / ((n : ℝ) * ρ)) *
        potentialGradientEnergy n V (fun z => F (magnitudeVector z)) := by
  have hfin := rhoConvex_potentialPartition_lt_top n hn ρ hρ hV hrot hc
  rw [potential_magnitude_entropy_eq_radiusProduct n hn hV.continuous hrot hfin
    F hF.continuous hs C hb,
    potential_magnitude_gradient_energy_eq_radiusProduct n hn hV.continuous hrot hfin
      F hF hs hLip]
  exact rhoConvex_radiusProduct_lsi n hn ρ hρ hV hrot hc F hF hLip C hC hb

/-- The paper's smooth compact radial observables, with all profile regularity
and boundedness derived from the observable itself. -/
theorem rhoConvex_potential_smooth_radial_lsi (n : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : Configuration n → ℝ) (hf : IsSmoothCompactSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    squareEntropy (potentialMeasure n V) f ≤
      (2 / ((n : ℝ) * ρ)) * potentialGradientEnergy n V f := by
  have hF := contDiff_magnitudeProfile f hf.1
  have hsupp := compactSupport_magnitudeProfile f hf.2.1
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hsupp hF (by simp)
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hF.continuous
  have he : f = (fun z => magnitudeProfile f (magnitudeVector z)) := by
    funext z
    exact radial_eq_magnitudeProfile f hr z
  have hb : ∀ r, |magnitudeProfile f r| ≤ max C 0 := by
    intro r
    have hh : |magnitudeProfile f r| ≤ C := by simpa only [Real.norm_eq_abs] using hC r
    exact hh.trans (le_max_left _ _)
  have ht := rhoConvex_potential_radial_lsi n hn ρ hρ hV hrot hc
    (magnitudeProfile f) (hF.of_le (by simp)) (magnitudeProfile_symmetric f hf.2.2)
    hK (max C 0) (le_max_right _ _) hb
  rwa [← he] at ht

#print axioms rhoConvex_potential_radial_lsi
end
end GinibrePoincare
