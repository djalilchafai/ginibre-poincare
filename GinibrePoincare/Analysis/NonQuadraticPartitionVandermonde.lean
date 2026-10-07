module

public import GinibrePoincare.Analysis.NonQuadraticPartitionMonomials
public import GinibrePoincare.Analysis.NonQuadraticAlternatedMonomialPolynomial

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

def partitionWeightedMonomialVector (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (i : Fin n) : PlanarLebesgueL2 :=
  (potentialPartition_weightedMonomial_memLp n hn hV hr hfin i).toLp _

theorem partitionWeightedMonomialVector_mem (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤)
    (i : Fin n) : partitionWeightedMonomialVector n hn hV hr hfin i ∈ planarWeightedMonomialVectors n V := by
  refine ⟨i.val, 1, ?_, ?_⟩
  · simpa only [one_mul] using potentialPartition_weightedMonomial_memLp n hn hV hr hfin i
  · unfold partitionWeightedMonomialVector
    apply MemLp.toLp_congr
    exact ae_of_all _ (fun z => by simp)

def partitionWeightedMonomialProduct (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) : PlanarPiLebesgueL2 n :=
  l2PiProductVector (fun _ => (volume : Measure ℂ)) (partitionWeightedMonomialVector n hn hV hr hfin)

theorem partitionWeightedMonomialProduct_coeFn (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    (partitionWeightedMonomialProduct n hn hV hr hfin : Configuration n → ℂ) =ᵐ[volume]
      (fun z => (∏ i, z i ^ i.val) * piPotentialHalfWeight n n V z) := by
  have hi (i : Fin n) : (partitionWeightedMonomialVector n hn hV hr hfin i : ℂ → ℂ) =ᵐ[volume]
      (fun z => z ^ i.val * planarPotentialHalfWeight n V z) :=
    (potentialPartition_weightedMonomial_memLp n hn hV hr hfin i).coeFn_toLp
  have hall : ∀ᵐ z ∂Measure.pi (fun _ : Fin n => (volume : Measure ℂ)), ∀ i,
      partitionWeightedMonomialVector n hn hV hr hfin i (z i) =
        z i ^ i.val * planarPotentialHalfWeight n V (z i) :=
    ae_all_iff.mpr (fun i => (Measure.quasiMeasurePreserving_eval (fun _ => (volume : Measure ℂ)) i).ae_eq_comp (hi i))
  rw [volume_pi]
  filter_upwards [l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ))
    (partitionWeightedMonomialVector n hn hV hr hfin), hall] with z hz hh
  change l2PiProductVector _ _ z = _
  rw [hz]
  simp only [hh, Finset.prod_mul_distrib, piPotentialHalfWeight]

theorem vandermonde_eq_signed_monomial_sum {n : ℕ} (z : Configuration n) :
    vandermonde z = ∑ σ : ParticlePermutation n, permutationSign σ * ∏ i, z (σ i) ^ i.val := by
  unfold vandermonde
  rw [Matrix.det_apply']
  simp only [Matrix.vandermonde_apply, permutationSign]

def partitionWeightedVandermondeL2 (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) : PlanarPiLebesgueL2 n :=
  (Fintype.card (ParticlePermutation n) : ℂ) •
    volumeAlternationOperator n (partitionWeightedMonomialProduct n hn hV hr hfin)

theorem partitionWeightedVandermondeL2_coeFn (n : ℕ) (hn : 0 < n) {V : Potential}
    (hV : Continuous V) (hr : IsRotationalPotential V) (hfin : potentialPartition n V < ⊤) :
    (partitionWeightedVandermondeL2 n hn hV hr hfin : Configuration n → ℂ) =ᵐ[volume]
      (fun z => vandermonde z * piPotentialHalfWeight n n V z) := by
  have he := volumeAlternationOperator_coeFn (partitionWeightedMonomialProduct n hn hV hr hfin) _
    (partitionWeightedMonomialProduct_coeFn n hn hV hr hfin)
  filter_upwards [Lp.coeFn_smul (Fintype.card (ParticlePermutation n) : ℂ)
    (volumeAlternationOperator n (partitionWeightedMonomialProduct n hn hV hr hfin)), he] with z hz hh
  unfold partitionWeightedVandermondeL2
  rw [hz]
  change (Fintype.card (ParticlePermutation n) : ℂ) * _ = _
  rw [hh, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_mul,
    vandermonde_eq_signed_monomial_sum]
  simp only [piPotentialHalfWeight_permute, Finset.sum_mul, permute]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem planarPiBergmanProjection_commutes_alternation {d : ℕ}
    (n : ℕ) (V : Potential) (hV : ContDiff ℝ 2 V) :
    (planarPiBergmanProjection (m := d) n V hV).comp (volumeAlternationOperator (d+1)) =
      (volumeAlternationOperator (d+1)).comp (planarPiBergmanProjection n V hV) := by
  apply ContinuousLinearMap.ext
  intro F
  simp only [volumeAlternationOperator, ContinuousLinearMap.comp_apply, smul_apply, sum_apply,
    map_smul, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  exact DFunLike.congr_fun (planarPiBergmanProjection_commutes_permutation n V hV σ) F

theorem partitionWeightedVandermondeL2_fixed {d : ℕ} {V : Potential}
    (hV : ContDiff ℝ 2 V) (hr : IsRotationalPotential V) (hfin : potentialPartition (d+1) V < ⊤) :
    planarPiBergmanProjection (d+1) V hV
      (partitionWeightedVandermondeL2 (d+1) (by omega) hV.continuous hr hfin) =
      partitionWeightedVandermondeL2 (d+1) (by omega) hV.continuous hr hfin := by
  let F := partitionWeightedMonomialProduct (d+1) (by omega) hV.continuous hr hfin
  have hf : planarPiBergmanProjection (d+1) V hV F = F := by
    apply planarPiWeightedMonomialVector_fixed (d+1) V hV (fun a ha z => hr a z ha)
    exact ⟨partitionWeightedMonomialVector (d+1) (by omega) hV.continuous hr hfin,
      fun i => partitionWeightedMonomialVector_mem (d+1) (by omega) hV.continuous hr hfin i, rfl⟩
  change planarPiBergmanProjection (d+1) V hV
    ((Fintype.card (ParticlePermutation (d+1)) : ℂ) • volumeAlternationOperator (d+1) F) = _
  rw [map_smul]
  have he := DFunLike.congr_fun (planarPiBergmanProjection_commutes_alternation (d+1) V hV) F
  change planarPiBergmanProjection (d+1) V hV (volumeAlternationOperator (d+1) F) =
    volumeAlternationOperator (d+1) (planarPiBergmanProjection (d+1) V hV F) at he
  rw [he, hf]
  rfl

end
end GinibrePoincare
