module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLiftBoundedLSI
public import GinibrePoincare.Analysis.AlternativeBakryEmeryRadiusLaw
@[expose] public section
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The paper's actual single-radius law inherits LSI from its strongly convex
Euclidean lift. No quantile transport or supplied diffusion is used. -/
theorem bakryEmery_kostlan_radius_bounded_lsi
    (n k : ℕ) (hn : 0 < n) (ρ : ℝ) (hρ : 0 < ρ)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) {K : ℝ≥0} (hLip : LipschitzWith K f)
    (C : ℝ) (hb : ∀ r, ‖f r‖ ≤ C) :
    squareEntropy ((potentialSquaredRadiusLaw n k V).map Real.sqrt) f ≤
      (2/((n:ℝ)*ρ)) * ∫ r, (deriv f r)^2 ∂(potentialSquaredRadiusLaw n k V).map Real.sqrt := by
  let E := EuclideanSpace ℝ (Fin (k+1) × Fin 2)
  let μ := bakryEmeryNormalizedGibbs (volume : Measure E) (bakryEmeryEuclideanLiftPotential n V)
  have hmap : μ.map norm = (potentialSquaredRadiusLaw n k V).map Real.sqrt :=
    bakryEmeryEuclideanGibbs_radius_law n k hn ρ hρ V hV.continuous hrot hc
  have he : squareEntropy (μ.map norm) f = squareEntropy μ (fun x : E => f ‖x‖) :=
    squareEntropy_map μ norm continuous_norm.measurable.aemeasurable f
      (hf.continuous.pow 2).aestronglyMeasurable
      (continuous_square_mul_log hf.continuous).aestronglyMeasurable
  have hg : (∫ x : E, ‖gradient (fun y : E => f ‖y‖) x‖^2 ∂μ) =
      ∫ r, (deriv f r)^2 ∂μ.map norm := by
    rw [integral_congr_ae (bakryEmeryEuclideanGibbs_radius_gradient_energy_ae n k V f hf)]
    exact (integral_map continuous_norm.measurable.aemeasurable
      ((hf.continuous_deriv (by norm_num)).pow 2).aestronglyMeasurable).symm
  have h := bakryEmeryEuclideanLift_boundedLipschitz_square_lsi n (k+1) hn (by omega)
    ρ hρ V hV hrot hc (fun x : E => f ‖x‖) (LipschitzWith.of_dist_le_mul (fun x y => (hLip.dist_le_mul ‖x‖ ‖y‖).trans
      (mul_le_mul_of_nonneg_left (dist_norm_norm_le x y) K.coe_nonneg))) C
    (fun x => hb ‖x‖)
  change squareEntropy μ (fun x : E => f ‖x‖) ≤ _ at h
  rw [←he,hg,hmap] at h
  exact h

#print axioms bakryEmery_kostlan_radius_bounded_lsi
end
end GinibrePoincare
