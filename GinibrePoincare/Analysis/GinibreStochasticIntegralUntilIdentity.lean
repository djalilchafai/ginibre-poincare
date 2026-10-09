module

public import GinibrePoincare.Analysis.GinibreStochasticContinuousLocalIdentity
public import GinibrePoincare.Analysis.GinibreStochasticProbabilityRestriction

@[expose] public section

/-! # Identifying continuous integral limits before a random time

For each deterministic `t`, restrict the two approximation sequences to
`E = {ω | t ≤ σ ω}` by indicators. Their finite sums agree on `E`, and their
indicator limits therefore agree almost everywhere by uniqueness of limits
in measure. The terminal event needs no adaptedness or predictability.

The continuous-identity theorem upgrades these individual deterministic-time
identities to one full-measure event valid for every time up to `σ`. The
bound `σ ≤ T` lets times beyond the horizon be dismissed and ensures the
required sequence limits are available for all relevant times. -/
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreContinuous_probability_limits_eq_until
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (S Q : ℝ≥0 → ℕ → Ω → ℝ) (I J : ℝ≥0 → Ω → ℝ)
    (hIC : ∀ᵐ ω ∂P, Continuous (fun t => I t ω))
    (hJC : ∀ᵐ ω ∂P, Continuous (fun t => J t ω))
    (T : ℝ≥0) (σ : Ω → ℝ≥0) (hσ : ∀ ω, σ ω ≤ T)
    (hS : ∀ t ≤ T, TendstoInMeasure P (S t) atTop (I t))
    (hQ : ∀ t ≤ T, TendstoInMeasure P (Q t) atTop (J t))
    (hEq : ∀ t ≤ T, ∀ k ω, t ≤ σ ω → S t k ω=Q t k ω) :
    ∀ᵐ ω ∂P, ∀ t ≤ σ ω, I t ω=J t ω := by
  classical
  apply ginibre_ae_continuous_identity_until P I J σ hIC hJC
  intro t
  by_cases ht : t ≤ T
  · let E : Set Ω := {ω | t ≤ σ ω}
    have hp := ginibre_tendstoInMeasure_indicator P E (S t) (I t) (hS t ht)
    have hq := ginibre_tendstoInMeasure_indicator P E (Q t) (J t) (hQ t ht)
    have he : (fun k => E.indicator (S t k))=(fun k => E.indicator (Q t k)) := by
      funext k ω
      by_cases hω : ω ∈ E
      · simp only [Set.indicator_of_mem hω]
        exact hEq t ht k ω hω
      · simp only [Set.indicator_of_notMem hω]
    rw [he] at hp
    filter_upwards [tendstoInMeasure_ae_unique hp hq] with ω hω
    intro hts
    have hωE : ω ∈ E := hts
    simpa only [Set.indicator_of_mem hωE] using hω
  · exact Eventually.of_forall (fun ω hts => (ht (hts.trans (hσ ω))).elim)
end
end GinibrePoincare
