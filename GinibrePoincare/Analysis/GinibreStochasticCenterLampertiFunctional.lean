module

public import GinibrePoincare.Analysis.GinibreStochasticCenterLampertiGenerator
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

def ginibreCenterLampertiRiemannFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (k : ℕ) (p : ℝ≥0 → Configuration n) (t : ℝ≥0) : ℝ :=
  (Real.sqrt (ginibreCenterSquared n (p t))-Real.sqrt (ginibreCenterSquared n z)-
    ∑ i : Fin (k+1), ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (p (ginibreUniformBrownianTime t k i)))*((t : ℝ)/((k : ℝ)+1))) /
        Real.sqrt (2*α/(n : ℝ))

def ginibreCenterLampertiPathFunctional (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → Configuration n) (t : ℝ≥0) : ℝ :=
  limUnder atTop (fun k => ginibreCenterLampertiRiemannFunctional n α z k p t)

theorem ginibreCenterLampertiRiemannFunctional_measurable (n : ℕ) (α : ℝ)
    (z : Configuration n) (k : ℕ) (t : ℝ≥0) :
    Measurable (fun p => ginibreCenterLampertiRiemannFunctional n α z k p t) := by
  have hr (s : ℝ≥0) : Measurable (fun p : ℝ≥0 → Configuration n => ginibreCenterSquared n (p s)) :=
    (contDiff_ginibreCenterSquared n).continuous.measurable.comp (measurable_pi_apply s)
  have hg : Measurable (fun p : ℝ≥0 → Configuration n => ∑ i : Fin (k+1),
      ginibreLampertiCenterDrift n α (ginibreCenterSquared n (p (ginibreUniformBrownianTime t k i)))*
        ((t : ℝ)/((k : ℝ)+1))) := by
    apply Finset.measurable_sum
    intro i hi
    exact ((ginibreLampertiCenterDrift_measurable n α).comp (hr _)).mul_const _
  exact (((Real.continuous_sqrt.measurable.comp (hr t)).sub measurable_const).sub hg).div_const _

theorem ginibreCenterLampertiPathFunctional_measurable (n : ℕ) (α : ℝ) (z : Configuration n) :
    Measurable (ginibreCenterLampertiPathFunctional n α z) := by
  apply measurable_pi_lambda
  intro t
  exact (StronglyMeasurable.limUnder (fun k =>
    (ginibreCenterLampertiRiemannFunctional_measurable n α z k t).stronglyMeasurable)).measurable

theorem ginibreCenterLampertiPathFunctional_eq_integral (n : ℕ) (α : ℝ) (z : Configuration n)
    (p : ℝ≥0 → Configuration n) (hp : Continuous p) (hpos : ∀ s, 0 < ginibreCenterSquared n (p s))
    (t : ℝ≥0) :
    ginibreCenterLampertiPathFunctional n α z p t =
      (Real.sqrt (ginibreCenterSquared n (p t))-Real.sqrt (ginibreCenterSquared n z)-
        ∫ s in (0 : ℝ)..t, ginibreLampertiCenterDrift n α (ginibreCenterSquared n (p s.toNNReal))) /
          Real.sqrt (2*α/(n : ℝ)) := by
  let w := fun s : ℝ => ginibreLampertiCenterDrift n α (ginibreCenterSquared n (p s.toNNReal))
  have hw : Continuous w := (ginibreLampertiCenterDrift_continuousOn n α).comp_continuous
    ((contDiff_ginibreCenterSquared n).continuous.comp (hp.comp continuous_real_toNNReal))
    (fun s => hpos _)
  have h := itoContinuousScalarRiemann_fin_tendsto w t hw.continuousOn
  have hl : Tendsto (fun k => ginibreCenterLampertiRiemannFunctional n α z k p t) atTop
      (𝓝 ((Real.sqrt (ginibreCenterSquared n (p t))-Real.sqrt (ginibreCenterSquared n z)-
        ∫ s in (0 : ℝ)..t, w s)/Real.sqrt (2*α/(n : ℝ)))) := by
    have hc : Tendsto (fun _ : ℕ => Real.sqrt (ginibreCenterSquared n (p t))-Real.sqrt (ginibreCenterSquared n z))
        atTop (𝓝 (Real.sqrt (ginibreCenterSquared n (p t))-Real.sqrt (ginibreCenterSquared n z))) := tendsto_const_nhds
    simpa only [ginibreCenterLampertiRiemannFunctional,w,Real.toNNReal_coe] using
      (hc.sub h).div_const (Real.sqrt (2*α/(n : ℝ)))
  exact hl.limUnder_eq
#print axioms ginibreCenterLampertiPathFunctional_eq_integral
#print axioms ginibreCenterLampertiPathFunctional_measurable
end
end GinibrePoincare
