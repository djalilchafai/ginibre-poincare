module

public import GinibrePoincare.Analysis.NonQuadraticPiBergmanMonomials

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

def volumeAlternationOperator (d : ℕ) :
    PlanarPiLebesgueL2 d →L[ℂ] PlanarPiLebesgueL2 d :=
  ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) •
    ∑ σ : ParticlePermutation d, permutationSign σ • (volumePermutationL2 σ).toContinuousLinearMap

theorem volumeAlternationOperator_fixed {d : ℕ} (F : PlanarPiLebesgueL2 d)
    (hF : ∀ σ : ParticlePermutation d, volumePermutationL2 σ F = permutationSign σ • F) :
    volumeAlternationOperator d F = F := by
  have hs (σ : ParticlePermutation d) : permutationSign σ * permutationSign σ = 1 := by
    unfold permutationSign
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simp only [volumeAlternationOperator, sum_apply, smul_apply]
  change ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) •
    (∑ σ : ParticlePermutation d, permutationSign σ • volumePermutationL2 σ F) = F
  simp_rw [hF, smul_smul, hs, one_smul]
  rw [Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [Finset.card_univ]
  have hcard : (Fintype.card (ParticlePermutation d) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_smul, inv_mul_cancel₀ hcard, one_smul]

def planarPiAlternatedWeightedMonomialVectors (d n : ℕ) (V : ℂ → ℝ) : Set (PlanarPiLebesgueL2 d) :=
  volumeAlternationOperator d '' planarPiWeightedMonomialVectors d n V

theorem planarPiBergman_alternating_mem_alternated_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z)
    (F : PlanarPiLebesgueL2 (d+1))
    (hF : ∀ σ : ParticlePermutation (d+1), volumePermutationL2 σ F = permutationSign σ • F) :
    planarPiBergmanProjection n V hV F ∈
      (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  let K := (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n V)).topologicalClosure
  let A := K.comap (volumeAlternationOperator (d+1)).toLinearMap
  have hK : IsClosed (K : Set (PlanarPiLebesgueL2 (d+1))) :=
    (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n V)).isClosed_topologicalClosure
  have hA : IsClosed (A : Set (PlanarPiLebesgueL2 (d+1))) :=
    hK.preimage (volumeAlternationOperator (d+1)).continuous
  have hb : Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V) ≤ A := by
    apply Submodule.span_le.mpr
    intro u hu
    exact (Submodule.span ℂ (planarPiAlternatedWeightedMonomialVectors (d+1) n V)).le_topologicalClosure
      (Submodule.subset_span ⟨u, hu, rfl⟩)
  have hle := (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure_minimal hb hA
  have hx := hle (planarPiBergmanProjection_mem_weighted_monomial_closure n V hV hr F)
  change volumeAlternationOperator (d+1) (planarPiBergmanProjection n V hV F) ∈ K at hx
  rw [volumeAlternationOperator_fixed _ (fun σ =>
    planarPiBergmanProjection_preserves_alternating n V hV F hF σ)] at hx
  exact hx
end
end GinibrePoincare
