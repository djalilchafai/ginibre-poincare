module

public import GinibrePoincare.Analysis.GinibreConjugationGeometry

@[expose] public section

/-! # Exact phase covariance of closed homogeneous quotient projections -/
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

/-- The actual orthogonal projection onto a homogeneous quotient closure
commutes with every unit global phase. -/
theorem ginibreGlobalPhaseL2_comm_quotientDegreeProjection {n : ℕ} (hn : 0 < n)
    (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (ginibreMeasure n)) :
    ginibreGlobalPhaseL2 hn u hu
        ((ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection x) =
      (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection
        (ginibreGlobalPhaseL2 hn u hu x) := by
  let U := (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule
  let T := ginibreGlobalPhaseL2 hn u hu
  have he : ∀ y ∈ U, T y = u ^ d • y := fun y hy =>
    ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n d hn hy u hu
  have hu0 : u ≠ 0 := by
    intro hz
    simp [hz] at hu
  have hmap : U.map T.toLinearMap = U := by
    apply le_antisymm
    · rintro y ⟨z, hz, rfl⟩
      change T z ∈ U
      rw [he z hz]
      exact U.smul_mem _ hz
    · intro y hy
      refine ⟨(u ^ d)⁻¹ • y, U.smul_mem _ hy, ?_⟩
      change T ((u ^ d)⁻¹ • y) = y
      rw [he _ (U.smul_mem _ hy), smul_smul, mul_inv_cancel₀ (pow_ne_zero _ hu0), one_smul]
  letI : (U.map T.toLinearMap).HasOrthogonalProjection := hmap.symm ▸ inferInstance
  calc
    T (U.starProjection x) = (U.map T.toLinearMap).starProjection (T x) := T.map_starProjection U x
    _ = U.starProjection (T x) := by simpa only [hmap]

/-- Projection onto degree d extracts its exact phase character from every
ambient L² vector. -/
theorem ginibre_quotientDegreeProjection_globalPhase {n : ℕ} (hn : 0 < n)
    (d : ℕ) (u : ℂ) (hu : ‖u‖ = 1) (x : Lp ℂ 2 (ginibreMeasure n)) :
    (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection
      (ginibreGlobalPhaseL2 hn u hu x) =
      u ^ d • (ginibreFiniteQuotientDegreeClosedSpan n d hn).toSubmodule.starProjection x := by
  rw [← ginibreGlobalPhaseL2_comm_quotientDegreeProjection]
  exact ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n d hn
    (Submodule.starProjection_apply_mem _ _) u hu

end
end GinibrePoincare
