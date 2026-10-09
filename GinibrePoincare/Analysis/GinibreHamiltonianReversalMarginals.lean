module

public import GinibrePoincare.Analysis.GinibreHamiltonianKilledExhaustionIntegration

@[expose] public section

open Set MeasureTheory
namespace GinibrePoincare
noncomputable section
local instance ginibreReversalMarginalsMeasurable (n : ℕ) (T : ℝ) :
    MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance ginibreReversalMarginalsBorel (n : ℕ) (T : ℝ) :
    BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩

/-- Actual reversal of a compact path law gives its stationary endpoint law. -/
theorem ginibreHamiltonian_reversal_endpoint_marginal (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure C(Icc (0 : ℝ) T, Configuration n))
    (hrev : μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT))=μ) :
    μ.map (fun x => x ⟨T, hT, le_rfl⟩)=μ.map (fun x => x ⟨0, le_rfl, hT⟩) := by
  have he : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) => x ⟨0, le_rfl, hT⟩) :=
    (continuous_eval_const _).measurable
  have hr : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime T hT)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T hT)).measurable
  have hh := congrArg (fun ν : Measure C(Icc (0 : ℝ) T, Configuration n) =>
    ν.map (fun x => x ⟨0, le_rfl, hT⟩)) hrev
  rw [Measure.map_map he hr] at hh
  have hf : ((fun x : C(Icc (0 : ℝ) T, Configuration n) => x ⟨0, le_rfl, hT⟩) ∘
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => x.comp (ginibreHamiltonianCompactReverseTime T hT))) =
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => x ⟨T, hT, le_rfl⟩) := by
    funext x
    change x ((ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩)=x ⟨T, hT, le_rfl⟩
    have ht : (ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩=⟨T, hT, le_rfl⟩ := by
      apply Subtype.ext
      change T-0=T
      ring
    rw [ht]
  rw [hf] at hh
  exact hh

/-- Reversal also gives the literal symmetry of the joint endpoint measure. -/
theorem ginibreHamiltonian_reversal_joint_endpoint (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (μ : Measure C(Icc (0 : ℝ) T, Configuration n))
    (hrev : μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT))=μ) :
    μ.map (fun x => (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩))=
    μ.map (fun x : C(Icc (0 : ℝ) T, Configuration n) => (x ⟨T, hT, le_rfl⟩, x ⟨0, le_rfl, hT⟩)) := by
  have he : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩)) :=
    (continuous_eval_const _).measurable.prodMk (continuous_eval_const _).measurable
  have hr : Measurable (fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      x.comp (ginibreHamiltonianCompactReverseTime T hT)) :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T hT)).measurable
  have hh := congrArg (fun ν : Measure C(Icc (0 : ℝ) T, Configuration n) =>
    ν.map (fun x => (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩))) hrev
  rw [Measure.map_map he hr] at hh
  have hf : ((fun x : C(Icc (0 : ℝ) T, Configuration n) =>
      (x ⟨0, le_rfl, hT⟩, x ⟨T, hT, le_rfl⟩)) ∘
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => x.comp (ginibreHamiltonianCompactReverseTime T hT))) =
      (fun x : C(Icc (0 : ℝ) T, Configuration n) => (x ⟨T, hT, le_rfl⟩, x ⟨0, le_rfl, hT⟩)) := by
    funext x
    have ht : (ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩=⟨T, hT, le_rfl⟩ := by
      apply Subtype.ext
      change T-0=T
      ring
    have hz : (ginibreHamiltonianCompactReverseTime T hT) ⟨T, hT, le_rfl⟩=⟨0, le_rfl, hT⟩ := by
      apply Subtype.ext
      change T-T=0
      ring
    change (x ((ginibreHamiltonianCompactReverseTime T hT) ⟨0, le_rfl, hT⟩),
      x ((ginibreHamiltonianCompactReverseTime T hT) ⟨T, hT, le_rfl⟩)) = _
    rw [ht, hz]
  rw [hf] at hh
  exact hh.symm

#print axioms ginibreHamiltonian_reversal_endpoint_marginal
#print axioms ginibreHamiltonian_reversal_joint_endpoint
end
end GinibrePoincare
