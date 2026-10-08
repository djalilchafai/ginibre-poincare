module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalSurvival
public import GinibrePoincare.Analysis.GinibreHamiltonianReversalMarginals
@[expose] public section
open Set MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance bakryGibbsExhaustion_pathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsExhaustion_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

/-- Countable compact-ball exhaustion passes actual killed reversals to full
path reversal. This integration lemma requires the killed identities; the
concrete stochastic proof supplies them separately. -/
theorem bakryEmeryGibbs_full_reverse_of_killed_reversals (n : ℕ) (T : ℝ≥0)
    (μ : Measure C(Icc (0 : ℝ) (T : ℝ), Configuration n))
    (hKilled : ∀ k : ℕ,
      (μ.restrict (bakryEmeryGibbsCompactSurvival n T (k : ℝ))).map
        (fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)) =
      μ.restrict (bakryEmeryGibbsCompactSurvival n T (k : ℝ))) :
    μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)) = μ := by
  let r : C(Icc (0 : ℝ) (T : ℝ), Configuration n) → C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
    fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)
  have hr : Measurable r :=
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T T.property)).measurable
  have hi : Function.Involutive r := by
    intro x
    ext t j
    change x ((ginibreHamiltonianCompactReverseTime T T.property)
      ((ginibreHamiltonianCompactReverseTime T T.property) t)) j = x t j
    have he : (ginibreHamiltonianCompactReverseTime T T.property)
        ((ginibreHamiltonianCompactReverseTime T T.property) t) = t := by
      apply Subtype.ext
      change (T : ℝ)-((T : ℝ)-t.val)=t.val
      ring
    rw [he]
  let e := MeasurableEquiv.ofInvolutive r hi hr
  let S : ℕ → Set C(Icc (0 : ℝ) (T : ℝ), Configuration n) :=
    fun k => bakryEmeryGibbsCompactSurvival n T (k : ℝ)
  have hpre (k : ℕ) : e ⁻¹' S k = S k := by
    ext x
    exact bakryEmeryGibbsCompactSurvival_reverse n T k x
  have hCov : (⋃ k, S k) = univ := bakryEmeryGibbsCompactSurvival_exhaustion n T
  have hEq : (μ.map e).restrict (⋃ k, S k) = μ.restrict (⋃ k, S k) := by
    apply Measure.restrict_iUnion_congr.mpr
    intro k
    rw [e.restrict_map,hpre]
    exact hKilled k
  rw [hCov,Measure.restrict_univ,Measure.restrict_univ] at hEq
  exact hEq

#print axioms bakryEmeryGibbs_full_reverse_of_killed_reversals
end
end GinibrePoincare
