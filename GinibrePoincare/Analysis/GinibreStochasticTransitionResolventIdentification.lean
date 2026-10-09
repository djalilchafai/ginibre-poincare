module

public import GinibrePoincare.Analysis.GinibreStochasticTransitionResolventOperator
public import GinibrePoincare.Analysis.GinibreStochasticTransitionCompactResolvent
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticBoundedAdjointIdentification

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Identification of the original stochastic resolvent on bounded symmetric inputs.
All local regularity and energy properties of its literal bounded representative
are derived from the actual compact adjoint equation. -/
theorem ginibreOriginalStochasticL2Resolvent_eq_analytic_bounded {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (hα : 0<(α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i x t => B i t x) P) (f : ginibreFullSymmetricValues n)
    (A : ℝ) (hb : ∀ᵐ z ∂ginibreMeasure n, ‖f.val z‖≤A) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f.val =
      (ginibreFullSymmetricResolvent n hn f).val := by
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (Nat.cast_pos.mpr hn)
  obtain ⟨v, hv, hvb, hfv⟩ := ginibreBoundedLp_measurable_version hn f.val A hb
  obtain ⟨hrm, hrb, hRr⟩ := ginibreOriginalStochasticL2Resolvent_bounded_representative
    hn α P B hB hiB hc f.val v hfv hv (max A 0) hvb
  let r := fun z => ∫ t in Ioi (0 : ℝ), ((α : ℝ)/(n : ℝ))*Real.exp (-((α : ℝ)/(n : ℝ))*t)*
    ginibreStationaryContinuousTransitionMean α B P v t z
  have hr : MemLp r 2 (ginibreMeasure n) := MemLp.of_bound hrm.aestronglyMeasurable (max A 0) (ae_of_all _ hrb)
  have hRp : ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f.val=hr.toLp r := by
    apply Lp.ext
    exact hRr.trans hr.coeFn_toLp.symm
  have heq : ∀ θ : Configuration n → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ {z | CollisionFree z} →
      (∫ z, r z*θ z ∂ginibreMeasure n)-(∫ z, r z*ginibrePregenerator n θ z ∂ginibreMeasure n)=
        ∫ z, f.val z*θ z ∂ginibreMeasure n := by
    intro θ hθ hcθ hs
    have htest : IsGinibreCollisionFreeCompactTest θ := ⟨hθ, hcθ, by
      intro z hz
      exact (collisionFree_iff_not_mem_collisionSet z).mp (hs hz)⟩
    have he := ginibreOriginalStochasticL2Resolvent_compact_adjoint_integral hn α hα P B hB hiB f.val θ htest
    have h1 : (∫ z, ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f.val z*θ z ∂ginibreMeasure n)=
        ∫ z, r z*θ z ∂ginibreMeasure n := integral_congr_ae (hRr.mono fun z hz => by dsimp only; rw [hz])
    have h2 : (∫ z, ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f.val z*ginibrePregenerator n θ z ∂ginibreMeasure n)=
        ∫ z, r z*ginibrePregenerator n θ z ∂ginibreMeasure n := integral_congr_ae (hRr.mono fun z hz => by dsimp only; rw [hz])
    exact h1 ▸ h2 ▸ he
  rw [hRp]
  exact ginibreTransitionAnalytic_bounded_adjoint_identification n hn f r hr (max A 0) (le_max_right _ _) hrb heq

/-- The original stochastic normalized Laplace integral equals the actual
analytic unit resolvent on every symmetric Ginibre L² value. -/
theorem ginibreOriginalStochasticL2Resolvent_eq_analytic {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (α : ℝ≥0) (hα : 0<(α : ℝ)) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hiB : iIndepFun (fun i x t => B i t x) P) (f : ginibreFullSymmetricValues n) :
    ginibreOriginalStochasticL2Resolvent hn α P B hB hiB ((α : ℝ)/(n : ℝ)) f.val =
      (ginibreFullSymmetricResolvent n hn f).val := by
  have hc : 0<(α : ℝ)/(n : ℝ) := div_pos hα (Nat.cast_pos.mpr hn)
  let R := (ginibreOriginalStochasticL2ResolventOperator hn α P B hB hiB ((α : ℝ)/(n : ℝ)) hc).comp
    (ginibreFullSymmetricValues n).subtypeL
  let S := (ginibreFullSymmetricValues n).subtypeL.comp (ginibreFullSymmetricResolvent n hn)
  have he : R=S := ginibreSymmetricSource_operators_eq_of_bounded_values n R S (by
    intro u hu
    obtain ⟨A, hA⟩ := hu
    exact ginibreOriginalStochasticL2Resolvent_eq_analytic_bounded hn α hα P B hB hiB u A hA)
  exact congrArg (fun Q => Q f) he

#print axioms ginibreOriginalStochasticL2Resolvent_eq_analytic_bounded
#print axioms ginibreOriginalStochasticL2Resolvent_eq_analytic
end
end GinibrePoincare
