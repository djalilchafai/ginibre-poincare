module

public import GinibrePoincare.Analysis.GeneralPotentialVandermondeSymmetry

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def volumeGlobalPhaseL2 {n : ℕ} (u : ℂ) (hu : ‖u‖ = 1) :
    Lp ℂ 2 (configurationVolume n) →ₗᵢ[ℂ] Lp ℂ 2 (configurationVolume n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (globalPhase u) (measurePreserving_globalPhase_configurationVolume n u hu)

def potentialGlobalPhaseL2 (n : ℕ) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (u : ℂ) (hu : ‖u‖ = 1) :
    Lp ℂ 2 (potentialMeasure n V) →ₗᵢ[ℂ] Lp ℂ 2 (potentialMeasure n V) :=
  Lp.compMeasurePreservingₗᵢ ℂ (globalPhase u) (measurePreserving_globalPhase_potentialMeasure n hV hrot u hu)

theorem potentialVandermondeMultiplier_globalPhase (n : ℕ) (V : Potential)
    (hrot : IsRotationalPotential V) (u : ℂ) (hu : ‖u‖ = 1) (z : Configuration n) :
    potentialVandermondeMultiplier n V (globalPhase u z) =
      u ^ vandermondeDegree n * potentialVandermondeMultiplier n V z := by
  have hs : (∑ i : Fin n, V (globalPhase u z i)) = ∑ i : Fin n, V (z i) := by
    apply Finset.sum_congr rfl
    intro i _
    exact hrot u (z i) hu
  unfold potentialVandermondeMultiplier
  rw [hs, vandermonde_globalPhase, ← vandermondeDegree_eq_sum_Ioi_card]
  ring

theorem volumeGlobalPhaseL2_potentialVandermonde {n : ℕ} (hn : 0 < n) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (potentialMeasure n V)) :
    volumeGlobalPhaseL2 u hu (potentialVandermondeL2 n hn hV hfin x) =
      u ^ vandermondeDegree n •
        potentialVandermondeL2 n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x) := by
  apply Lp.ext
  have hsrc := (measurePreserving_globalPhase_configurationVolume n u hu).quasiMeasurePreserving.ae_eq_comp (potentialVandermondeL2_coeFn_public n hn hV hfin x)
  have hcomp := (configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin).ae_eq
      (Lp.coeFn_compMeasurePreserving x (measurePreserving_globalPhase_potentialMeasure n hV hrot u hu))
  filter_upwards [Lp.coeFn_compMeasurePreserving (potentialVandermondeL2 n hn hV hfin x)
      (measurePreserving_globalPhase_configurationVolume n u hu), hsrc,
    Lp.coeFn_smul (u ^ vandermondeDegree n)
      (potentialVandermondeL2 n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x)),
    potentialVandermondeL2_coeFn_public n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x),
    hcomp] with z hleft hsource hright htarget hx
  change (volumeGlobalPhaseL2 u hu (potentialVandermondeL2 n hn hV hfin x)) z = _
  change (volumeGlobalPhaseL2 u hu (potentialVandermondeL2 n hn hV hfin x)) z =
    (potentialVandermondeL2 n hn hV hfin x) (globalPhase u z) at hleft
  rw [hleft, hright]
  change (potentialVandermondeL2 n hn hV hfin x) (globalPhase u z) =
    (u ^ vandermondeDegree n) * (potentialVandermondeL2 n hn hV hfin (potentialGlobalPhaseL2 n hV hrot u hu x)) z
  change (potentialVandermondeL2 n hn hV hfin x) (globalPhase u z) =
    potentialVandermondeMultiplier n V (globalPhase u z) * x (globalPhase u z) at hsource
  change (potentialGlobalPhaseL2 n hV hrot u hu x) z = x (globalPhase u z) at hx
  rw [hsource, htarget, hx]
  rw [potentialVandermondeMultiplier_globalPhase n V hrot u hu z]
  ring

end
end GinibrePoincare
