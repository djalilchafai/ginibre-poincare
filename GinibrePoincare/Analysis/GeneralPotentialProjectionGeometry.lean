module

public import GinibrePoincare.Analysis.GeneralPotentialProjectionPermutation
public import GinibrePoincare.Analysis.GeneralPotentialVandermondeCentered
public import GinibrePoincare.Analysis.GeneralPotentialLpConjugation

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem potentialCenteredL2_permutation (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V))
    (hs : IsSymmetric f) (e : ParticlePermutation n) :
    potentialPermutationL2 n hV e (potentialCenteredL2 n hn hV hfin f hf) =
      potentialCenteredL2 n hn hV hfin f hf := by
  unfold potentialPermutationL2
  change Lp.compMeasurePreserving (permute e)
    (measurePreserving_permute_potentialMeasure n hV e) _ = _
  apply Lp.ext
  have hc := potentialCenteredL2_coeFn n hn hV hfin f hf
  filter_upwards [Lp.coeFn_compMeasurePreserving
    (potentialCenteredL2 n hn hV hfin f hf)
    (measurePreserving_permute_potentialMeasure n hV e), hc,
    (measurePreserving_permute_potentialMeasure n hV e).quasiMeasurePreserving.ae_eq_comp hc]
    with z hp hz hq
  rw [hp, hq, hz]
  simp only [Function.comp_apply]
  rw [hs e z]

theorem potentialVandermondeCentered_alternating (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V))
    (hs : IsSymmetric f) (e : ParticlePermutation n) :
    volumePermutationL2 e
      (potentialVandermondeL2 n hn hV hfin (potentialCenteredL2 n hn hV hfin f hf)) =
      permutationSign e •
        potentialVandermondeL2 n hn hV hfin (potentialCenteredL2 n hn hV hfin f hf) := by
  rw [potentialVandermondeL2_intertwines hn hV hfin,
    potentialCenteredL2_permutation n hn hV hfin f hf hs e]

theorem potentialCenteredL2_star (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hfin : potentialPartition n V < ⊤)
    (f : Configuration n → ℝ) (hf : MemLp f 2 (potentialMeasure n V)) :
    star (potentialCenteredL2 n hn hV hfin f hf) = potentialCenteredL2 n hn hV hfin f hf := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (potentialCenteredL2 n hn hV hfin f hf),
    potentialCenteredL2_coeFn n hn hV hfin f hf] with z hs hz
  rw [hs]
  simp only [Pi.star_apply, hz]
  exact Complex.conj_ofReal _

end
end GinibrePoincare
