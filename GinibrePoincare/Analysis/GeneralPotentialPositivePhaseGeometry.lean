module

public import GinibrePoincare.Analysis.GeneralPotentialProjectionPhase
public import GinibrePoincare.Analysis.GeneralPotentialLpConjugation

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def potentialPositivePhaseVectors (n : ℕ) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) : Set (Lp ℂ 2 (potentialMeasure n V)) :=
  {x | ∃ d : ℕ, 0 < d ∧ ∀ (a : ℂ) (ha : ‖a‖ = 1),
    potentialGlobalPhaseL2 n hV hrot a ha x = a ^ d • x}

theorem potentialPositivePhase_inner_star_zero {n d e : ℕ} {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hd : 0 < d) (he : 0 < e)
    (x y : Lp ℂ 2 (potentialMeasure n V))
    (hx : ∀ (a : ℂ) (ha : ‖a‖ = 1), potentialGlobalPhaseL2 n hV hrot a ha x = a ^ d • x)
    (hy : ∀ (a : ℂ) (ha : ‖a‖ = 1), potentialGlobalPhaseL2 n hV hrot a ha y = a ^ e • y) :
    inner ℂ x (star y) = 0 := by
  obtain ⟨a, ha, hpow⟩ := exists_unit_phase_pow_ne (d+e) 0 (by omega)
  have hs : potentialGlobalPhaseL2 n hV hrot a ha (star y) = conj (a^e) • star y := by
    rw [potentialGlobalPhaseL2_star, hy, complexLp_star_complex_smul]
  have hc : conj (a^d) * conj (a^e) ≠ 1 := by
    intro h
    apply hpow
    have hh : conj (a^(d+e)) = 1 := by simpa only [pow_add, map_mul] using h
    have hhh := congrArg (starRingEnd ℂ) hh
    simpa using hhh
  exact inner_eq_zero_of_isometry_eigencharacters (potentialGlobalPhaseL2 n hV hrot a ha)
    x (star y) (a^d) (conj (a^e)) (hx a ha) hs hc

end
end GinibrePoincare
