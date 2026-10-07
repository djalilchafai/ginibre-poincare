module

public import GinibrePoincare.Analysis.GeneralPotentialVandermondeInverse

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem measurePreserving_permute_configurationVolume {n : ℕ} (σ : ParticlePermutation n) :
    MeasurePreserving (permute σ) (configurationVolume n) (configurationVolume n) := by
  unfold configurationVolume
  rw [volume_pi]
  convert measurePreserving_piCongrLeft (fun _ : Fin n => (volume : Measure ℂ)) σ.symm using 1
  funext z
  exact (permutationMeasurableEquiv_apply σ z).symm

def volumePermutationL2 {n : ℕ} (σ : ParticlePermutation n) :
    Lp ℂ 2 (configurationVolume n) →ₗᵢ[ℂ] Lp ℂ 2 (configurationVolume n) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute σ) (measurePreserving_permute_configurationVolume σ)

def potentialPermutationL2 (n : ℕ) {V : Potential} (hV : Continuous V)
    (σ : ParticlePermutation n) :
    Lp ℂ 2 (potentialMeasure n V) →ₗᵢ[ℂ] Lp ℂ 2 (potentialMeasure n V) :=
  Lp.compMeasurePreservingₗᵢ ℂ (permute σ) (measurePreserving_permute_potentialMeasure n hV σ)

theorem potentialVandermondeMultiplier_permute {n : ℕ} (V : Potential)
    (σ : ParticlePermutation n) (z : Configuration n) :
    potentialVandermondeMultiplier n V (permute σ z) =
      permutationSign σ * potentialVandermondeMultiplier n V z := by
  have hs : (∑ i : Fin n, V (permute σ z i)) = ∑ i : Fin n, V (z i) := by
    simpa [permute] using Equiv.sum_comp σ (fun i => V (z i))
  unfold potentialVandermondeMultiplier
  rw [hs, vandermonde_permute]
  ring

theorem potentialVandermondeL2_intertwines {n : ℕ} (hn : 0 < n) {V : Potential} (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (σ : ParticlePermutation n) (u : Lp ℂ 2 (potentialMeasure n V)) :
    volumePermutationL2 σ (potentialVandermondeL2 n hn hV hfin u) =
      permutationSign σ •
        potentialVandermondeL2 n hn hV hfin (potentialPermutationL2 n hV σ u) := by
  unfold volumePermutationL2 potentialPermutationL2
  change Lp.compMeasurePreserving (permute σ)
      (measurePreserving_permute_configurationVolume σ) (potentialVandermondeL2 n hn hV hfin u) =
    permutationSign σ • potentialVandermondeL2 n hn hV hfin
      (Lp.compMeasurePreserving (permute σ)
        (measurePreserving_permute_potentialMeasure n hV σ) u)
  apply Lp.ext
  have hac := configurationVolume_absolutelyContinuous_potentialMeasure n hn hV hfin
  filter_upwards [Lp.coeFn_compMeasurePreserving
      (potentialVandermondeL2 n hn hV hfin u)
      (measurePreserving_permute_configurationVolume σ),
    (measurePreserving_permute_configurationVolume σ).quasiMeasurePreserving.ae_eq_comp
      (potentialVandermondeL2_coeFn_public n hn hV hfin u),
    potentialVandermondeL2_coeFn_public n hn hV hfin
      (Lp.compMeasurePreserving (permute σ)
        (measurePreserving_permute_potentialMeasure n hV σ) u),
    hac.ae_eq (Lp.coeFn_compMeasurePreserving u
      (measurePreserving_permute_potentialMeasure n hV σ)),
    Lp.coeFn_smul (permutationSign σ)
      (potentialVandermondeL2 n hn hV hfin
        (Lp.compMeasurePreserving (permute σ)
          (measurePreserving_permute_potentialMeasure n hV σ) u))] with
      z hleft hFu hFperm huperm hsmul
  rw [hleft, hFu, hsmul]
  simp only [Pi.smul_apply]
  rw [hFperm, huperm]
  simp only [Function.comp_apply, smul_eq_mul]
  rw [potentialVandermondeMultiplier_permute V]
  ring


end
end GinibrePoincare
