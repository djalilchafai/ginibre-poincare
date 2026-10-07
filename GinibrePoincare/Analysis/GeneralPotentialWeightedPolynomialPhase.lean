module

public import GinibrePoincare.Analysis.GeneralPotentialQuotientProjection
public import GinibrePoincare.Analysis.NonQuadraticAlternatedMonomialPolynomial
public import GinibrePoincare.Analysis.GeneralPotentialCenteredMean

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem piPotentialHalfWeight_globalPhase (n d : ℕ) {V : Potential}
    (hrot : IsRotationalPotential V) (a : ℂ) (ha : ‖a‖ = 1) (z : Configuration d) :
    piPotentialHalfWeight d n V (globalPhase a z) = piPotentialHalfWeight d n V z := by
  unfold piPotentialHalfWeight planarPotentialHalfWeight
  simp only [globalPhase_apply, hrot a _ ha]

theorem volumeGlobalPhaseL2_weighted_homogeneous {n d D : ℕ} {V : Potential}
    (hrot : IsRotationalPotential V) (P : ConfigurationPolynomial d) (hP : P.IsHomogeneous D)
    (F : PlanarPiLebesgueL2 d)
    (hF : (F : Configuration d → ℂ) =ᵐ[volume]
      fun z => MvPolynomial.eval z P * piPotentialHalfWeight d n V z)
    (a : ℂ) (ha : ‖a‖ = 1) : volumeGlobalPhaseL2 a ha F = a ^ D • F := by
  apply Lp.ext
  have hp := (measurePreserving_globalPhase_configurationVolume d a ha).quasiMeasurePreserving.ae_eq_comp hF
  filter_upwards [Lp.coeFn_compMeasurePreserving F
    (measurePreserving_globalPhase_configurationVolume d a ha), hp, hF,
    Lp.coeFn_smul (a ^ D) F] with z hc hp hz hs
  calc
    volumeGlobalPhaseL2 a ha F z = F (globalPhase a z) := hc
    _ = MvPolynomial.eval (globalPhase a z) P * piPotentialHalfWeight d n V (globalPhase a z) := hp
    _ = a ^ D * F z := by
      rw [hz, piPotentialHalfWeight_globalPhase n d hrot a ha z,
        isHomogeneousConfigurationPolynomial_of_isHomogeneous hP a z]
      ring
    _ = (a ^ D • F) z := hs.symm

theorem potentialInverseGauge_phase_degree {n D : ℕ} (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (hle : vandermondeDegree n ≤ D) (F : PlanarPiLebesgueL2 n)
    (hF : ∀ (a : ℂ) (ha : ‖a‖ = 1), volumeGlobalPhaseL2 a ha F = a ^ D • F)
    (a : ℂ) (ha : ‖a‖ = 1) :
    potentialGlobalPhaseL2 n hV hrot a ha ((potentialPiVandermondeL2Equiv n hn hV hfin).symm F) =
      a ^ (D - vandermondeDegree n) • (potentialPiVandermondeL2Equiv n hn hV hfin).symm F := by
  let E := potentialPiVandermondeL2Equiv n hn hV hfin
  have han : a ≠ 0 := by intro h; simp [h] at ha
  have he : volumeGlobalPhaseL2 a ha F = a ^ vandermondeDegree n •
      E (potentialGlobalPhaseL2 n hV hrot a ha (E.symm F)) := by
    have hh := volumeGlobalPhaseL2_potentialVandermonde hn hV hrot hfin a ha (E.symm F)
    change volumeGlobalPhaseL2 a ha (E (E.symm F)) = _ at hh
    rw [E.apply_symm_apply] at hh
    exact hh
  apply E.injective
  rw [E.map_smul, E.apply_symm_apply]
  have hh := congrArg (fun x => (a ^ vandermondeDegree n)⁻¹ • x) he
  rw [hF a ha] at hh
  simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ han), one_smul] at hh
  have hp : (a ^ vandermondeDegree n)⁻¹ * a ^ D = a ^ (D - vandermondeDegree n) := by
    rw [show D = vandermondeDegree n + (D - vandermondeDegree n) from (Nat.add_sub_of_le hle).symm,
      pow_add, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ han), one_mul]
    congr 1 <;> omega
  simpa only [hp] using hh.symm

theorem weightedPolynomialL2_eq_zero {n d : ℕ} {V : Potential}
    (F : PlanarPiLebesgueL2 d)
    (hF : (F : Configuration d → ℂ) =ᵐ[volume]
      fun z => MvPolynomial.eval z (0 : ConfigurationPolynomial d) * piPotentialHalfWeight d n V z) :
    F = 0 := by
  apply Lp.ext
  filter_upwards [hF, Lp.coeFn_zero ℂ 2 (volume : Measure (Configuration d))] with z hz hzero
  exact hz.trans (by simpa using hzero.symm)

end
end GinibrePoincare
