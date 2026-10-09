module

public import GinibrePoincare.Analysis.GinibreStochasticLampertiGenerator
public import GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import Mathlib.MeasureTheory.Function.FactorsThrough

@[expose] public section

/-! A genuine measurable Lamperti path functional, built from actual finite
Riemann sums, with no measurability assumption on an ordinary path integral. -/
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

theorem pairwiseRadius_recentered (n : ℕ) (z : Configuration n) :
    pairwiseRadius (recenteredConfiguration n z)=pairwiseRadius z := by
  simp only [pairwiseRadius_eq_radialObservable, radialObservable, recenteredSqNorm, recentered_idempotent]

def ginibreLampertiRiemannFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (k : ℕ) (p : ℝ≥0 → Configuration n) (t : ℝ≥0) : ℝ :=
  (Real.sqrt (pairwiseRadius (p t))-Real.sqrt (pairwiseRadius z)-
    ∑ i : Fin (k+1), ginibreLampertiRadialDrift n α
      (pairwiseRadius (p (ginibreUniformBrownianTime t k i)))*((t : ℝ)/((k : ℝ)+1))) /
        Real.sqrt (2*α/(n : ℝ))

def ginibreLampertiPathFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → Configuration n) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun k => ginibreLampertiRiemannFunctional n α z k p t)

theorem ginibreLampertiRiemannFunctional_measurable (n : ℕ) (α : ℝ)
    (z : Configuration n) (k : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreLampertiRiemannFunctional n α z k p t) := by
  have hr (s : ℝ≥0) : Measurable (fun p : ℝ≥0 → Configuration n => pairwiseRadius (p s)) :=
    (ginibre_contDiff_pairwiseRadius n).continuous.measurable.comp (measurable_pi_apply s)
  have hg : Measurable (fun p : ℝ≥0 → Configuration n => ∑ i : Fin (k+1),
      ginibreLampertiRadialDrift n α (pairwiseRadius (p (ginibreUniformBrownianTime t k i)))*
        ((t : ℝ)/((k : ℝ)+1))) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((ginibreLampertiRadialDrift_measurable n α).comp (hr _)).mul_const _
  exact (((Real.continuous_sqrt.measurable.comp (hr t)).sub measurable_const).sub hg).div_const _

theorem ginibreLampertiPathFunctional_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    Measurable (ginibreLampertiPathFunctional n α z) := by
  apply measurable_pi_lambda
  intro t
  exact (StronglyMeasurable.limUnder (fun k =>
    (ginibreLampertiRiemannFunctional_measurable n α z k t).stronglyMeasurable)).measurable

theorem ginibreLampertiPathFunctional_eq_integral (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → Configuration n) (hp : Continuous p) (hpos : ∀ s, 0 < pairwiseRadius (p s))
    (t : ℝ≥0) :
    ginibreLampertiPathFunctional n α z p t =
      (Real.sqrt (pairwiseRadius (p t))-Real.sqrt (pairwiseRadius z)-
        ∫ s in (0 : ℝ)..t, ginibreLampertiRadialDrift n α (pairwiseRadius (p s.toNNReal))) /
          Real.sqrt (2*α/(n : ℝ)) := by
  let w := fun s : ℝ => ginibreLampertiRadialDrift n α (pairwiseRadius (p s.toNNReal))
  have hw : Continuous w := (ginibreLampertiRadialDrift_continuousOn n α).comp_continuous
    ((ginibre_contDiff_pairwiseRadius n).continuous.comp (hp.comp continuous_real_toNNReal))
    (fun s => hpos _)
  have h := itoContinuousScalarRiemann_fin_tendsto w t hw.continuousOn
  have hl : Tendsto (fun k => ginibreLampertiRiemannFunctional n α z k p t) atTop
      (𝓝 ((Real.sqrt (pairwiseRadius (p t))-Real.sqrt (pairwiseRadius z)-
        ∫ s in (0 : ℝ)..t, w s)/Real.sqrt (2*α/(n : ℝ)))) := by
    have hc : Tendsto (fun _ : ℕ => Real.sqrt (pairwiseRadius (p t))-Real.sqrt (pairwiseRadius z))
        atTop (𝓝 (Real.sqrt (pairwiseRadius (p t))-Real.sqrt (pairwiseRadius z))) := tendsto_const_nhds
    simpa only [ginibreLampertiRiemannFunctional, w, Real.toNNReal_coe] using
      (hc.sub h).div_const (Real.sqrt (2*α/(n : ℝ)))
  exact hl.limUnder_eq
end
end GinibrePoincare
