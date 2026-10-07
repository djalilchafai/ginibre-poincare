module

public import GinibrePoincare.Analysis.BrownianIntegralGaussianChronology

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def chronologicalPrependFiltration {Ω : Type*} [MeasurableSpace Ω]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) : Filtration ℕ ‹MeasurableSpace Ω› :=
  ⟨fun n => Nat.casesOn n ⊥ (fun k => ℱ k),by
    intro i j hij
    cases i with
    | zero => exact bot_le
    | succ i =>
        cases j with
        | zero => omega
        | succ j => exact ℱ.mono (Nat.succ_le_succ_iff.mp hij),by
    intro n
    cases n with
    | zero => exact bot_le
    | succ n => exact ℱ.le n⟩

/-- The actual chronological innovation sum is independent of every actual
initial-past scalar variable, derived through genuine joint independence. -/
theorem chronologicalFresh_initial_prefix_independent
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›) (Z : ℕ → Ω → ℝ)
    (hZ : ∀ n, @Measurable Ω ℝ (ℱ (n+1)) _ (Z n))
    (hFresh : ∀ n (Y : Ω → ℝ), @Measurable Ω ℝ (ℱ n) _ Y → IndepFun Y (Z n) P)
    (Y : Ω → ℝ) (hY : @Measurable Ω ℝ (ℱ 0) _ Y) (N : ℕ) :
    IndepFun Y (fun ω => ∑ k ∈ Finset.range N, Z k ω) P := by
  classical
  let X : ℕ → Ω → ℝ := fun n => Nat.casesOn n Y Z
  have hi : iIndepFun X P := by
    apply chronologicalFresh_iIndepFun P (chronologicalPrependFiltration ℱ) X
    · intro n
      cases n with
      | zero => exact hY
      | succ n => exact hZ n
    · intro n V hV
      cases n with
      | zero =>
          apply (IndepFun_iff_Indep V Y P).mpr
          exact indep_of_indep_of_le_left (indep_bot_left (MeasurableSpace.comap Y inferInstance)) hV.comap_le
      | succ n => exact hFresh n V hV
  have hXm : ∀ n, Measurable (X n) := by
    intro n
    cases n with
    | zero => exact hY.mono (ℱ.le 0) le_rfl
    | succ n => exact (hZ n).mono (ℱ.le (n+1)) le_rfl
  let S := (Finset.range N).image Nat.succ
  have h0 : 0 ∉ S := by simp [S]
  have hh := hi.indepFun_finsetSum_of_notMem hXm h0
  have he : (∑ k ∈ S, X k) = (fun ω => ∑ k ∈ Finset.range N, Z k ω) := by
    rw [Finset.sum_image (fun a ha b hb hab => Nat.succ_injective hab)]
    funext ω
    simp [X,Finset.sum_apply]
  rw [he] at hh
  exact hh.symm

/-- Actual chronological adaptive unit innovations remain independent of
ANY actual initial-past random variable, including entire past trajectories. -/
theorem brownianUnitGridPrefix_independent_past
    {Ω ι A : Type*} [MeasurableSpace Ω] [Fintype ι] [DecidableEq ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (u : ℕ → Ω → EuclideanSpace ℝ ι) (τ : ℕ → ℝ≥0) (hτ : Monotone τ)
    (hu : ∀ k, @Measurable Ω (EuclideanSpace ℝ ι)
      (ginibreBrownianAugmentedFiltration B P hB (τ k)) _ (u k))
    (hunit : ∀ k ω, ‖u k ω‖ = 1) (i : ι) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB (τ 0)) _ Y) (N : ℕ) :
    IndepFun Y (brownianUnitGridPrefix B u τ N) P := by
  classical
  apply indepFun_iff_measure_inter_preimage_eq_mul.mpr
  intro A C hA hC
  let V : Ω → ℝ := (Y ⁻¹' A).indicator (fun _ => 1)
  have hV : @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB (τ 0)) _ V :=
    measurable_const.indicator (hY hA)
  have hi := chronologicalFresh_initial_prefix_independent P
    (sampledMartingaleFiltration (ginibreBrownianAugmentedFiltration B P hB) τ hτ)
    (brownianUnitGridInnovation B u τ)
    (brownianUnitGridInnovation_measurable_at_end B P hB u τ hτ hu)
    (fun k Z hZ => (brownianUnitGridInnovation_gaussian_independent B P hB hind u τ hu hunit k Z hZ i).2)
    V hV N
  have hp : V ⁻¹' ({1} : Set ℝ) = Y ⁻¹' A := by
    ext ω
    by_cases hω : Y ω ∈ A <;> simp [V,hω]
  have hh := hi.measure_inter_preimage_eq_mul ({1} : Set ℝ) C (measurableSet_singleton 1) hC
  rw [hp] at hh
  exact hh

end
end GinibrePoincare
