module

public import GinibrePoincare.Analysis.GaussianHermitePhase
public import GinibrePoincare.Analysis.VandermondeL2

@[expose] public section

/-! # Exact phase intertwining of the actual Vandermonde isometry -/
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000

/-- The Vandermonde isometry shifts every actual phase character by its
holomorphic degree. -/
theorem gaussianGlobalPhaseL2_normalizedVandermonde {n : ℕ} (hn : 0 < n)
    (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (ginibreMeasure n)) :
    gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x) =
      u ^ vandermondeDegree n •
        normalizedVandermondeL2 n hn (ginibreGlobalPhaseL2 hn u hu x) := by
  apply Lp.ext
  have hsrc := (measurePreserving_globalPhase_complexGaussianMeasure hn u hu).quasiMeasurePreserving.ae_eq_comp (normalizedVandermondeL2_coeFn_public n hn x)
  have hcomp := (complexGaussianMeasure_absolutelyContinuous_ginibreMeasure
    (ginibreMassEvaluation n hn)).ae_eq
      (Lp.coeFn_compMeasurePreserving x (measurePreserving_globalPhase_ginibreMeasure hn u hu))
  filter_upwards [Lp.coeFn_compMeasurePreserving (normalizedVandermondeL2 n hn x)
      (measurePreserving_globalPhase_complexGaussianMeasure hn u hu), hsrc,
    Lp.coeFn_smul (u ^ vandermondeDegree n)
      (normalizedVandermondeL2 n hn (ginibreGlobalPhaseL2 hn u hu x)),
    normalizedVandermondeL2_coeFn_public n hn (ginibreGlobalPhaseL2 hn u hu x),
    hcomp] with z hleft hsource hright htarget hx
  change (gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x)) z = _
  change (gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x)) z =
    (normalizedVandermondeL2 n hn x) (globalPhase u z) at hleft
  rw [hleft, hright]
  change (normalizedVandermondeL2 n hn x) (globalPhase u z) =
    (u ^ vandermondeDegree n) * (normalizedVandermondeL2 n hn (ginibreGlobalPhaseL2 hn u hu x)) z
  change (normalizedVandermondeL2 n hn x) (globalPhase u z) =
    normalizedVandermondeMultiplier n (globalPhase u z) * x (globalPhase u z) at hsource
  change (ginibreGlobalPhaseL2 hn u hu x) z = x (globalPhase u z) at hx
  rw [hsource, htarget, hx]
  unfold normalizedVandermondeMultiplier
  rw [vandermonde_globalPhase, ← vandermondeDegree_eq_sum_Ioi_card]
  ring

/-- Exact transformed character of an arbitrary actual Ginibre phase eigenvector. -/
theorem gaussianGlobalPhaseL2_normalizedVandermonde_character {n r s : ℕ} (hn : 0 < n)
    (x : Lp ℂ 2 (ginibreMeasure n))
    (hx : ∀ (u : ℂ) (hu : ‖u‖ = 1), ginibreGlobalPhaseL2 hn u hu x =
      (u ^ r * (conj u) ^ s) • x) :
    ∀ (u : ℂ) (hu : ‖u‖ = 1),
      gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn x) =
        (u ^ (vandermondeDegree n + r) * (conj u) ^ s) •
          normalizedVandermondeL2 n hn x := by
  intro u hu
  rw [gaussianGlobalPhaseL2_normalizedVandermonde, hx u hu, map_smul, smul_smul]
  rw [pow_add, mul_assoc]

end
end GinibrePoincare
