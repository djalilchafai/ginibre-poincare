module

public import GinibrePoincare.Analysis.NonQuadraticWeightedMonomialRepresentatives
public import GinibrePoincare.Analysis.NonQuadraticAlternatingPhasePolynomial

@[expose] public section

open MeasureTheory Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

theorem volumeAlternationOperator_coeFn {d : ℕ}
    (F : PlanarPiLebesgueL2 d) (f : Configuration d → ℂ) (hf : (F : Configuration d → ℂ) =ᵐ[volume] f) :
    (volumeAlternationOperator d F : Configuration d → ℂ) =ᵐ[volume]
      (fun x => ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) *
        ∑ σ : ParticlePermutation d, permutationSign σ * f (permute σ x)) := by
  let U := fun σ : ParticlePermutation d => permutationSign σ • volumePermutationL2 σ F
  have hi (σ : ParticlePermutation d) : (U σ : Configuration d → ℂ) =ᵐ[volume]
      (fun x => permutationSign σ * f (permute σ x)) := by
    have hp := (measurePreserving_permute_configurationVolume σ).quasiMeasurePreserving.ae_eq_comp hf
    have hc := Lp.coeFn_compMeasurePreserving F (measurePreserving_permute_configurationVolume σ)
    filter_upwards [Lp.coeFn_smul (permutationSign σ) (volumePermutationL2 σ F), hp, hc] with x hs hx hh
    rw [hs]
    change permutationSign σ * volumePermutationL2 σ F x = _
    change F (permute σ x) = f (permute σ x) at hx
    rw [show volumePermutationL2 σ F x = F (permute σ x) from hh, hx]
  have hall : ∀ᵐ x ∂(volume : Measure (Configuration d)), ∀ σ, U σ x =
      permutationSign σ * f (permute σ x) := ae_all_iff.mpr hi
  have ha : volumeAlternationOperator d F =
      ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) • ∑ σ, U σ := by
    simp only [volumeAlternationOperator, U, sum_apply, smul_apply]
    congr 1
  rw [ha]
  filter_upwards [Lp.coeFn_smul ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) (∑ σ, U σ),
    complexLp_finset_sum_coeFn volume Finset.univ U, hall] with x hs hx hh
  rw [hs]
  change ((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) * (∑ σ, U σ) x = _
  rw [hx]
  simp only [hh]

def alternatedMonomialPolynomial {d : ℕ} (p : Fin d → ℕ) (c : ℂ) : ConfigurationPolynomial d :=
  MvPolynomial.C (((Fintype.card (ParticlePermutation d) : ℂ)⁻¹) * c) *
    ∑ σ : ParticlePermutation d, MvPolynomial.C (permutationSign σ) *
      ∏ i : Fin d, (MvPolynomial.X (σ i)) ^ p i

theorem planarPiAlternatedWeightedMonomialVector_polynomial {d : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (F : PlanarPiLebesgueL2 d) (hF : F ∈ planarPiAlternatedWeightedMonomialVectors d n V) :
    ∃ p : Fin d → ℕ, ∃ c : ℂ,
      (F : Configuration d → ℂ) =ᵐ[volume]
        (fun x => MvPolynomial.eval x (alternatedMonomialPolynomial p c) * piPotentialHalfWeight d n V x) := by
  obtain ⟨G, hG, rfl⟩ := hF
  obtain ⟨p, c, hg⟩ := planarPiWeightedMonomialVector_coeFn n V G hG
  refine ⟨p, c, ?_⟩
  have he := volumeAlternationOperator_coeFn G _ hg
  apply he.mono
  intro x hx
  rw [hx]
  simp only [alternatedMonomialPolynomial, map_mul, map_sum, map_prod, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, piPotentialHalfWeight_permute]
  simp only [Finset.mul_sum, Finset.sum_mul, permute]
  apply Finset.sum_congr rfl
  intro σ _
  ring

theorem alternatedMonomialPolynomial_homogeneous {d : ℕ} (p : Fin d → ℕ) (c : ℂ) :
    (alternatedMonomialPolynomial p c).IsHomogeneous (∑ i, p i) := by
  apply MvPolynomial.IsHomogeneous.C_mul
  apply MvPolynomial.IsHomogeneous.sum
  intro σ _
  apply MvPolynomial.IsHomogeneous.C_mul
  exact MvPolynomial.IsHomogeneous.prod _ _ p (fun i _ => MvPolynomial.isHomogeneous_X_pow (σ i) (p i))

theorem permutationSign_mul_general {d : ℕ} (σ τ : ParticlePermutation d) :
    permutationSign (σ*τ) = permutationSign σ * permutationSign τ := by
  simp [permutationSign, map_mul]

theorem permutationSign_sq_general {d : ℕ} (σ : ParticlePermutation d) :
    permutationSign σ * permutationSign σ = 1 := by
  unfold permutationSign
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem alternatedMonomialPolynomial_alternating {d : ℕ} (p : Fin d → ℕ) (c : ℂ) :
    IsAlternatingConfigurationPolynomial (alternatedMonomialPolynomial p c) := by
  intro τ
  apply MvPolynomial.funext
  intro x
  rw [eval_permuteConfigurationPolynomial]
  simp only [alternatedMonomialPolynomial, map_mul, map_sum, map_prod, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X, permute]
  have hs : (∑ σ : ParticlePermutation d, permutationSign (τ*σ) * ∏ i, x ((τ*σ) i) ^ p i) =
      ∑ σ : ParticlePermutation d, permutationSign σ * ∏ i, x (σ i) ^ p i :=
    Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => permutationSign σ * ∏ i, x (σ i) ^ p i)
  rw [← hs]
  simp only [Finset.mul_sum, permutationSign_mul_general, Equiv.Perm.mul_apply]
  apply Finset.sum_congr rfl
  intro σ _
  have ht := permutationSign_sq_general τ
  have ht2 : permutationSign τ ^ 2 = 1 := by simpa only [pow_two] using ht
  ring_nf
  rw [ht2, mul_one]


theorem planarPiAlternatedWeightedMonomialVector_homogeneous_alternating {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (F : PlanarPiLebesgueL2 d)
    (hF : F ∈ planarPiAlternatedWeightedMonomialVectors d n V) :
    ∃ D : ℕ, ∃ P : ConfigurationPolynomial d, P.IsHomogeneous D ∧
      IsAlternatingConfigurationPolynomial P ∧
      (F : Configuration d → ℂ) =ᵐ[volume]
        (fun x => MvPolynomial.eval x P * piPotentialHalfWeight d n V x) := by
  obtain ⟨p, c, he⟩ := planarPiAlternatedWeightedMonomialVector_polynomial n V F hF
  exact ⟨∑ i, p i, alternatedMonomialPolynomial p c,
    alternatedMonomialPolynomial_homogeneous p c, alternatedMonomialPolynomial_alternating p c, he⟩

theorem planarPiAlternatedWeightedMonomialVector_vandermonde_quotient {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (F : PlanarPiLebesgueL2 d)
    (hF : F ∈ planarPiAlternatedWeightedMonomialVectors d n V) :
    ∃ D : ℕ, ∃ Q : ConfigurationPolynomial d, IsSymmetricConfigurationPolynomial Q ∧
      (polynomialVandermonde d * Q).IsHomogeneous D ∧
      (F : Configuration d → ℂ) =ᵐ[volume]
        (fun x => vandermonde x * MvPolynomial.eval x Q * piPotentialHalfWeight d n V x) := by
  obtain ⟨D, P, hh, ha, he⟩ := planarPiAlternatedWeightedMonomialVector_homogeneous_alternating n V F hF
  obtain ⟨Q, hQ, hP⟩ := alternating_polynomial_vandermonde_division ha
  refine ⟨D, Q, hQ, hP ▸ hh, ?_⟩
  simpa only [hP, map_mul, eval_polynomialVandermonde] using he

end
end GinibrePoincare
