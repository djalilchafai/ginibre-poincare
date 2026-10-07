module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic
public import Mathlib.Topology.Algebra.Module.Basic

@[expose] public section

namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

/-- A closed linear target containing multilinear products of generators
contains products from each actual closed linear span. -/
theorem continuousMultilinear_mem_of_closed_factor_spans
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℂ (E i)]
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (M : ContinuousMultilinearMap ℂ E H) (S : ∀ i, Set (E i))
    (K : Submodule ℂ H) (hK : IsClosed (K : Set H))
    (hb : ∀ u : ∀ i, E i, (∀ i, u i ∈ S i) → M u ∈ K)
    (u : ∀ i, E i) (hu : ∀ i, u i ∈ (Submodule.span ℂ (S i)).topologicalClosure) : M u ∈ K := by
  have hh (s : Finset ι) : ∀ v : ∀ i, E i,
      (∀ i ∈ s, v i ∈ (Submodule.span ℂ (S i)).topologicalClosure) →
      (∀ i ∉ s, v i ∈ S i) → M v ∈ K := by
    induction s using Finset.induction_on with
    | empty =>
      intro v _ hv
      exact hb v (fun i => hv i (by simp))
    | @insert i s his ih =>
      intro v hv hs
      let L : E i →L[ℂ] H :=
        { __ := M.toMultilinearMap.toLinearMap v i
          cont := M.cont.comp (continuous_const.update i continuous_id) }
      let A := K.comap L.toLinearMap
      have hA : IsClosed (A : Set (E i)) := hK.preimage L.continuous
      have hbase : S i ⊆ A := by
        intro a ha
        apply ih (Function.update v i a)
        · intro j hjs
          rw [Function.update_of_ne (show j ≠ i from fun h => his (h ▸ hjs))]
          exact hv j (Finset.mem_insert_of_mem hjs)
        · intro j hjs
          by_cases hji : j = i
          · subst j
            simpa only [Function.update_self] using ha
          · rw [Function.update_of_ne hji]
            exact hs j (by simp [hjs, hji])
      have hspan : Submodule.span ℂ (S i) ≤ A := Submodule.span_le.mpr hbase
      have hvi : v i ∈ A := hA.closure_subset_iff.mpr hspan (hv i (Finset.mem_insert_self ..))
      change M (Function.update v i (v i)) ∈ K at hvi
      simpa only [Function.update_eq_self] using hvi
  exact hh Finset.univ u (fun i _ => hu i) (fun i hi => False.elim (hi (Finset.mem_univ i)))
end
end GinibrePoincare
