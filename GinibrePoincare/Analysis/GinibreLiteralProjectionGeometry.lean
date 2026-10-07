module

public import GinibrePoincare.Analysis.GinibreConjugationGeometry

@[expose] public section

/-! # Projection residual identities on the concrete smooth Ginibre core

These are the projection-norm formulas in arXiv:2608.19358v2,
Lemma 2.7(3), on the smooth core and the proved closed holomorphic
polynomial subspace. They do not identify the representative-level
infimum over all entire functions defined in `HolomorphicDistance`.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem ginibre_core_holomorphic_projection_residual_identity {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    let u := centeredObservableL2 hn f hf
    let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u
    let r := u - h - star h
    ‖u - h‖ ^ 2 = smoothGinibreVariance n f / 2 + ‖r‖ ^ 2 / 2 := by
  dsimp
  let u := centeredObservableL2 hn f hf
  let h := (ginibreHolomorphicAmbientClosedSpan n hn).starProjection u
  have hh : h ∈ (ginibreHolomorphicAmbientClosedSpan n hn).toSubmodule :=
    Submodule.starProjection_apply_mem _ u
  have ho : inner ℂ h (u - h) = 0 := by
    rw [← inner_conj_symm h (u - h), Submodule.starProjection_inner_eq_zero u h hh,
      map_zero]
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero h (u - h) ho
  have he : h + (u - h) = u := by abel
  rw [he] at hp
  have hnrm : ‖u‖ ^ 2 = smoothGinibreVariance n f := norm_sq_centeredObservableL2 hn f hf
  have hg := (centeredHolomorphicRemainderGeometry hn f hf).2.2.2
  change smoothGinibreVariance n f = 2 * ‖h‖ ^ 2 + ‖u - h - star h‖ ^ 2 at hg
  change ‖u - h‖ ^ 2 = smoothGinibreVariance n f / 2 + ‖u - h - star h‖ ^ 2 / 2
  nlinarith

theorem ginibre_core_holomorphic_projection_half_distance {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    smoothGinibreVariance n f / 2 ≤
      ‖centeredObservableL2 hn f hf -
        (ginibreHolomorphicAmbientClosedSpan n hn).starProjection (centeredObservableL2 hn f hf)‖ ^ 2 := by
  rw [ginibre_core_holomorphic_projection_residual_identity hn f hf]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (by norm_num))

#print axioms ginibre_core_holomorphic_projection_residual_identity
#print axioms ginibre_core_holomorphic_projection_half_distance
end
end GinibrePoincare
