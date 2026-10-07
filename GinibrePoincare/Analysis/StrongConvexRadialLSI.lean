module

public import GinibrePoincare.Analysis.StrongConvexRadialTransport
public import GinibrePoincare.Analysis.StrongConvexTransportMeasure
public import GinibrePoincare.Analysis.StrongConvexTransportLSI
public import GinibrePoincare.Analysis.StrongConvexRadialLaw

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

/-- Sharp non-quadratic positive-radius LSI for the actual normalized Kostlan
density. Strong convexity, quantile contraction, and the image law are all
proved rather than supplied as certificates. -/
theorem rhoConvex_radial_lsi (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfl : MemLp f 2 ((volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))))
    (hfd : MemLp (deriv f) 2 ((volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r)))) :
    let ν := (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))
    Integrable (fun r => f r ^ 2 * Real.log (f r ^ 2)) ν ∧
      squareEntropy ν f ≤ (2 / ((n : ℝ) * ρ)) * ∫ r, (deriv f r) ^ 2 ∂ν := by
  obtain ⟨T, hTc, hmap, hb⟩ := rhoConvex_radial_gaussian_transport n k hn ρ hρ hV hrot hc
  let ν := (volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
    (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))
  have hκ : 0 < (n : ℝ) * ρ := mul_pos (Nat.cast_pos.mpr hn) hρ
  have hsqrt : 0 < Real.sqrt ((n : ℝ) * ρ) := Real.sqrt_pos.mpr hκ
  have h := standardGaussian_transport_lsi ν T hTc hmap
    (Real.sqrt ((n : ℝ) * ρ))⁻¹ (inv_nonneg.mpr hsqrt.le) hb f hf hfl hfd
  change Integrable (fun r => f r ^ 2 * Real.log (f r ^ 2)) ν ∧
    squareEntropy ν f ≤ (2 / ((n : ℝ) * ρ)) * ∫ r, (deriv f r) ^ 2 ∂ν
  refine ⟨h.1, ?_⟩
  calc
    _ ≤ (2 * (Real.sqrt ((n : ℝ) * ρ))⁻¹ ^ 2) * ∫ r, (deriv f r) ^ 2 ∂ν := h.2
    _ = _ := by rw [inv_pow, Real.sq_sqrt hκ.le]; ring

/-- The same sharp LSI, stated on the existing actual Kostlan radius law. -/
theorem rhoConvex_kostlan_radius_lsi (n k : ℕ) (hn : 0 < n)
    (ρ : ℝ) (hρ : 0 < ρ) {V : Potential} (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfl : MemLp f 2 ((potentialSquaredRadiusLaw n k V).map Real.sqrt))
    (hfd : MemLp (deriv f) 2 ((potentialSquaredRadiusLaw n k V).map Real.sqrt)) :
    Integrable (fun r => f r ^ 2 * Real.log (f r ^ 2))
      ((potentialSquaredRadiusLaw n k V).map Real.sqrt) ∧
      squareEntropy ((potentialSquaredRadiusLaw n k V).map Real.sqrt) f ≤
        (2 / ((n : ℝ) * ρ)) * ∫ r, (deriv f r) ^ 2 ∂(potentialSquaredRadiusLaw n k V).map Real.sqrt := by
  have hi := rhoConvexPotential_radial_density_integrable n k hn ρ hρ hV hrot hc
  have he := radialConfinementProbabilityDensity_eq_sqrt_map n k V hV.continuous hi
  have hv : MemLp f 2 ((volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))) := he.symm ▸ hfl
  have hd : MemLp (deriv f) 2 ((volume : Measure ℝ).withDensity (fun r => ENNReal.ofReal
      (radialConfinementProbabilityDensity n k (fun t : ℝ => V (t : ℂ)) r))) := he.symm ▸ hfd
  have h := rhoConvex_radial_lsi n k hn ρ hρ hV hrot hc f hf hv hd
  dsimp only at h
  rw [he] at h
  exact h

#print axioms rhoConvex_kostlan_radius_lsi
#print axioms rhoConvex_radial_lsi
end
end GinibrePoincare
