module

public import GinibrePoincare.Analysis.EquilibriumProbability
public import GinibrePoincare.Analysis.GlobalPhaseAction
public import GinibrePoincare.Analysis.PairwiseRadius

@[expose] public section

open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Rotate the relative configuration by a quarter turn, fixing its center. -/
def ginibreRelativeQuarterTurn (n : ℕ) (z : Configuration n) : Configuration n :=
  fun i => coordinateSum z/(n : ℂ)+Complex.I*recenteredConfiguration n z i

theorem coordinateSum_ginibreRelativeQuarterTurn {n : ℕ} (hn : 0<n) (z : Configuration n) :
    coordinateSum (ginibreRelativeQuarterTurn n z)=coordinateSum z := by
  have hnC : (n : ℂ)≠0 := by exact_mod_cast hn.ne'
  simp only [ginibreRelativeQuarterTurn, coordinateSum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,← Finset.mul_sum]
  change (n : ℂ)*(coordinateSum z/(n : ℂ))+Complex.I*coordinateSum (recenteredConfiguration n z)=coordinateSum z
  rw [coordinateSum_recentered, mul_zero, add_zero]
  exact mul_div_cancel₀ _ hnC

theorem recentered_ginibreRelativeQuarterTurn {n : ℕ} (hn : 0<n) (z : Configuration n) :
    recenteredConfiguration n (ginibreRelativeQuarterTurn n z)=fun i => Complex.I*recenteredConfiguration n z i := by
  ext i
  simp only [recenteredConfiguration, projectToOrthogonal]
  rw [coordinateSum_ginibreRelativeQuarterTurn hn]
  simp only [ginibreRelativeQuarterTurn, recenteredConfiguration, projectToOrthogonal]
  ring

theorem pairwiseRadius_ginibreRelativeQuarterTurn (n : ℕ) (z : Configuration n) :
    pairwiseRadius (ginibreRelativeQuarterTurn n z)=pairwiseRadius z := by
  unfold pairwiseRadius
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro k hk
  have he : ginibreRelativeQuarterTurn n z j-ginibreRelativeQuarterTurn n z k=Complex.I*(z j-z k) := by
    simp only [ginibreRelativeQuarterTurn, recenteredConfiguration, projectToOrthogonal]
    ring
  rw [he, Complex.normSq_mul]
  simp

def recenteredQuarterTurn (n : ℕ) (w : zeroSumHyperplane n) : zeroSumHyperplane n := Complex.I • w

theorem measurePreserving_recenteredQuarterTurn {n : ℕ} (hn : 0<n) :
    MeasurePreserving (recenteredQuarterTurn n) (recenteredGinibreMeasure n) (recenteredGinibreMeasure n) := by
  have hm : Measurable (recenteredQuarterTurn n) := by
    unfold recenteredQuarterTurn
    exact ((continuous_const : Continuous (fun _ : zeroSumHyperplane n => Complex.I)).smul continuous_id).measurable
  have he : recenteredQuarterTurn n ∘ recenteredCoordinate n=recenteredCoordinate n ∘ globalPhase Complex.I := by
    funext z
    apply Subtype.ext
    ext i
    simp only [Function.comp_apply, recenteredQuarterTurn, recenteredCoordinate,
      Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, globalPhase, recenteredConfiguration,
      projectToOrthogonal, coordinateSum,← Finset.mul_sum]
    ring
  refine ⟨hm,?_⟩
  change ((ginibreMeasure n).map (recenteredCoordinate n)).map (recenteredQuarterTurn n)=_
  rw [Measure.map_map hm (measurable_recenteredCoordinate n), he,
    ← Measure.map_map (measurable_recenteredCoordinate n) (measurePreserving_globalPhase_ginibreMeasure hn Complex.I (by simp)).measurable,
    (measurePreserving_globalPhase_ginibreMeasure hn Complex.I (by simp)).map_eq]
  rfl

/-- Genuine Ginibre invariance under relative quarter-turn, obtained from the
actual center/relative product law and global-phase invariance of its marginal. -/
theorem measurePreserving_ginibreRelativeQuarterTurn {n : ℕ} (hn : 0<n) :
    MeasurePreserving (ginibreRelativeQuarterTurn n) (ginibreMeasure n) (ginibreMeasure n) := by
  letI := recenteredGinibreMeasure_isProbabilityMeasure n hn
  let e := equilibriumMeasurableCoordinates n hn
  have hE : MeasurePreserving e (ginibreMeasure n)
      (standardComplexGaussianMeasure.prod (recenteredGinibreMeasure n)) :=
    ⟨e.measurable, equilibrium_jointLaw n hn⟩
  have hP := (MeasurePreserving.id standardComplexGaussianMeasure).prod
    (measurePreserving_recenteredQuarterTurn hn)
  have hInv := MeasurePreserving.symm e hE
  convert hInv.comp (hP.comp hE) using 1
  funext z
  rfl

#print axioms measurePreserving_recenteredQuarterTurn
#print axioms measurePreserving_ginibreRelativeQuarterTurn
end
end GinibrePoincare
