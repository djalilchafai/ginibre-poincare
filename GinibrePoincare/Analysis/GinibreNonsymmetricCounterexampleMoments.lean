module

public import GinibrePoincare.Analysis.GinibreTwoRadiusEquilibriumLaw
public import GinibrePoincare.Analysis.GammaPolynomialMoments
public import GinibrePoincare.Analysis.GlobalPhaseAction
public import GinibrePoincare.Concrete.SmoothTarget

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreGamma_integrable_first (k : ℕ) (hk : 0<k) :
    Integrable (fun x:ℝ => x) (gammaMeasure k 1) := by
  simpa using Laguerre.integrable_pow_gamma k 1 hk

theorem ginibreGamma_integral_first (k : ℕ) (hk : 0<k) :
    (∫ x:ℝ, x ∂gammaMeasure k 1)=(k:ℝ) := by
  have hzero : Laguerre.gammaMoment k 0=1 := by
    simp [Laguerre.gammaMoment, Nat.factorial_ne_zero]
  simpa [hzero] using (Laguerre.integral_pow_gamma k 1 hk).trans
    (by rw [show 1=0+1 from rfl,Laguerre.gammaMoment_succ k 0 hk]; simp [hzero])

theorem ginibre_configurationNormSq_integrable (n : ℕ) (hn : 2≤n) :
    Integrable (configurationNormSq : Configuration n → ℝ) (ginibreMeasure n) := by
  have hn0 : 0<n := by omega
  have hc : Measurable (ginibreCenterSquared n) := by unfold ginibreCenterSquared coordinateSum; fun_prop
  have hr : Measurable (pairwiseRadius : Configuration n → ℝ) := by unfold pairwiseRadius; fun_prop
  have hiC : Integrable (ginibreCenterSquared n) (ginibreMeasure n) := by
    have h := ginibreGamma_integrable_first 1 (by omega)
    norm_num only [Nat.cast_one] at h
    rw [← ginibreCenterSquared_equilibrium_gamma n hn0] at h
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hc.aemeasurable).mp h
  have hiR : Integrable (pairwiseRadius : Configuration n → ℝ) (ginibreMeasure n) := by
    have h := ginibreGamma_integrable_first (recenteredGammaShape n) (recenteredGammaShape_pos n hn)
    rw [recenteredGammaShape_eq n hn0,← pairwiseRadius_ginibre_gamma n hn] at h
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hr.aemeasurable).mp h
  have he (z : Configuration n) : configurationNormSq z=
      (ginibreCenterSquared n z+pairwiseRadius z)/(n:ℝ) := by
    have h := pairwiseRadius_eq_normSq z
    dsimp [ginibreCenterSquared] at *
    field_simp
    nlinarith
  exact ((hiC.add hiR).div_const n).congr (Filter.Eventually.of_forall fun z => (he z).symm)

theorem ginibre_configurationNormSq_integral (n : ℕ) (hn : 2≤n) :
    (∫ z, configurationNormSq z ∂ginibreMeasure n)=((n:ℝ)+1)/2 := by
  have hn0 : 0<n := by omega
  have hc : Measurable (ginibreCenterSquared n) := by unfold ginibreCenterSquared coordinateSum; fun_prop
  have hr : Measurable (pairwiseRadius : Configuration n → ℝ) := by unfold pairwiseRadius; fun_prop
  have heC : (∫ z, ginibreCenterSquared n z ∂ginibreMeasure n)=1 := by
    have h := ginibreGamma_integral_first 1 (by omega)
    norm_num only [Nat.cast_one] at h
    rw [← ginibreCenterSquared_equilibrium_gamma n hn0,
      integral_map hc.aemeasurable (show AEStronglyMeasurable (fun x:ℝ => x) ((ginibreMeasure n).map (ginibreCenterSquared n)) from measurable_id.aestronglyMeasurable)] at h
    exact h
  have heR : (∫ z, pairwiseRadius z ∂ginibreMeasure n)=(recenteredGammaShape n:ℝ) := by
    have h := ginibreGamma_integral_first (recenteredGammaShape n) (recenteredGammaShape_pos n hn)
    rw [recenteredGammaShape_eq n hn0,← pairwiseRadius_ginibre_gamma n hn,
      integral_map hr.aemeasurable (show AEStronglyMeasurable (fun x:ℝ => x) ((ginibreMeasure n).map pairwiseRadius) from measurable_id.aestronglyMeasurable)] at h
    simpa only [recenteredGammaShape_eq n hn0] using h
  have hiC : Integrable (ginibreCenterSquared n) (ginibreMeasure n) := by
    have h := ginibreGamma_integrable_first 1 (by omega)
    norm_num only [Nat.cast_one] at h
    rw [← ginibreCenterSquared_equilibrium_gamma n hn0] at h
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hc.aemeasurable).mp h
  have hiR : Integrable (pairwiseRadius : Configuration n → ℝ) (ginibreMeasure n) := by
    have h := ginibreGamma_integrable_first (recenteredGammaShape n) (recenteredGammaShape_pos n hn)
    rw [recenteredGammaShape_eq n hn0,← pairwiseRadius_ginibre_gamma n hn] at h
    exact (integrable_map_measure measurable_id.aestronglyMeasurable hr.aemeasurable).mp h
  have he : (configurationNormSq : Configuration n → ℝ)=
      fun z => (ginibreCenterSquared n z+pairwiseRadius z)/(n:ℝ) := by
    funext z
    have h := pairwiseRadius_eq_normSq z
    dsimp [ginibreCenterSquared] at *
    field_simp
    nlinarith
  rw [he,integral_div,integral_add hiC hiR,heC,heR,recenteredGammaShape_eq n hn0]
  have hne : (n:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hn0)
  field_simp
  ring

#print axioms ginibre_configurationNormSq_integral

end
end GinibrePoincare
