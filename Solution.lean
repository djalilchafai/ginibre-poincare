module

public import GinibrePoincare.Analysis.GinibreEqualityWeakAffine

@[expose] public section

/-! # Proved Palomar statement
The compared theorem is the full symmetric weak-H¹ Poincaré inequality and
its affine equality classification (Theorem 1.1 of
https://arxiv.org/abs/2608.19358v2). The independent Challenge explicitly gives
the concrete probability law, the ordinary distributional gradient, and the
literal integral variance. The substantive development also proves the two
Theorem 1.9 deficits; those are not advertised by this Comparator configuration.
-/

open MeasureTheory
open scoped ENNReal ContDiff
namespace PalomarGinibre
open GinibrePoincare

/-- Full weak-H¹ symmetric Poincaré assertion and exact affine equality case.
Symmetry is imposed only on the observable; its weak gradient's corresponding
symmetry follows from uniqueness, rather than being an additional assumption. -/
def theoremOneOneStatement : Prop :=
  ∀ n : ℕ, 0 < n → ∀ u : Lp ℝ 2 (ginibreMeasure n),
    ∀ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      IsGinibreDistributionalGradient n u g →
      (∀ σ : ParticlePermutation n,
        (fun z => u (permute σ z)) =ᵐ[ginibreMeasure n] (u : Configuration n → ℝ)) →
      smoothGinibreVariance n u ≤ ginibreWeakEnergy n g / 2 ∧
        (smoothGinibreVariance n u = ginibreWeakEnergy n g / 2 ↔
          ∃ (a : ℝ) (c : ℂ), (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
            fun z => a + 2 * (c * coordinateSum z).re)


/-- The full weak-domain inequality and exhaustive affine equality case. -/
theorem theoremOneOne :
  ∀ n : ℕ, 0 < n → ∀ u : Lp ℝ 2 (ginibreMeasure n),
    ∀ g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (LocallyIntegrableOn u {z : Configuration n | CollisionFree z} volume ∧
        (∀ k : Fin n × Fin 2,
          LocallyIntegrableOn (fun z => g z k) {z : Configuration n | CollisionFree z} volume) ∧
        ∀ (k : Fin n × Fin 2) (θ : Configuration n → ℝ),
          ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ {z | CollisionFree z} →
            (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k))) →
      (∀ σ : ParticlePermutation n,
        (fun z => u (permute σ z)) =ᵐ[ginibreMeasure n] (u : Configuration n → ℝ)) →
      smoothGinibreVariance n u ≤ ((1 / (n : ℝ)) * ‖g‖ ^ 2) / 2 ∧
        (smoothGinibreVariance n u = ((1 / (n : ℝ)) * ‖g‖ ^ 2) / 2 ↔
          ∃ (a : ℝ) (c : ℂ), (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
            fun z => a + 2 * (c * coordinateSum z).re) := by
  intro n hn u g hu hsym
  have hs : IsGinibreSymmetricWeakPair (u, g) := by
    intro σ
    have hv : ginibreRealPermutationL2 σ u = u :=
      Lp.ext ((ginibreRealPermutationL2_ae σ u).trans (hsym σ))
    refine ⟨hv, ?_⟩
    have hp := ginibreDistributionalGradient_permute hn σ u g hu
    rw [hv] at hp
    exact ginibre_distributional_gradient_unique n hn u
      (ginibreGradientPermutationL2 σ g) g hp hu
  have hvar : ginibreL2Variance n hn u = smoothGinibreVariance n u := by
    rw [ginibreL2Variance, ← integral_square_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub u
      (ginibreRealConstantL2 n hn (ginibreL2Mean n u)),
      ginibreRealConstantL2_ae n hn (ginibreL2Mean n u)] with z hz hc
    rw [hz]
    simp only [Pi.sub_apply, hc]
    rfl
  constructor
  · rw [← hvar]
    exact ginibre_symmetric_weak_poincare hn u g hu hs
  · have heq := ginibreEquality_full_weak_affine_iff hn u g hu hs
    rw [hvar] at heq
    unfold ginibreWeakEnergy at heq
    constructor
    · intro h
      apply heq.mp
      linarith
    · intro h
      have he := heq.mpr h
      linarith

end PalomarGinibre

#print axioms PalomarGinibre.theoremOneOne
