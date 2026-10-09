module

public import GinibrePoincare.Analysis.GinibreStochasticCenterLampertiNoiseCoefficient
public import GinibrePoincare.Analysis.GinibreStochasticCenterLampertiRegularization
public import GinibrePoincare.Analysis.GinibreStochasticCenterZeroDirection

@[expose] public section

/-! Deterministic localization of the genuine regularized Itô coefficients on
positive-start compact intervals. No assertion about the drift at zero is used. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

theorem ginibreCenterRegularized_generator_interval
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (a t : ℝ≥0) (hat : a ≤ t)
    (hfree : ∀ u ∈ Icc a t, CollisionFree (X u))
    (hlow : ∀ u ∈ Icc a t, δ < ginibreCenterSquared n (X u)) :
    (∫ r in (a : ℝ)..t, ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) =
    ∫ r in (a : ℝ)..t, ginibreLampertiCenterDrift n α
      (ginibreCenterSquared n (X r.toNNReal)) := by
  apply intervalIntegral.integral_congr
  intro r hr
  rw [uIcc_of_le (show (a : ℝ) ≤ t from hat)] at hr
  have hu : r.toNNReal ∈ Icc a t := by
    constructor
    · exact_mod_cast (show (a : ℝ) ≤ (r.toNNReal : ℝ) by rw [Real.coe_toNNReal _ (a.coe_nonneg.trans hr.1)]; exact hr.1)
    · exact (Real.toNNReal_le_iff_le_coe).mpr hr.2
  exact ginibreCenterSquareRootRegularized_generator hn α hδ _ (hfree _ hu) (hlow _ hu)

theorem ginibreCenterRegularized_noise_coordinate_interval
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (a t u : ℝ≥0)
    (hlow : ∀ v ∈ Icc a t, δ < ginibreCenterSquared n (X v))
    (hu : u ∈ Icc a t) (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*(α : ℝ)/(n : ℝ)^2)*
      fderiv ℝ (ginibreCenterSquareRootRegularized n δ) (X u)
        (ginibreCoordinateDirection i) =
      Real.sqrt (2*(α : ℝ)/(n : ℝ))*ginibreCenterRadialDirection n e (X u) i := by
  rw [(ginibreCenterSquareRootRegularized_eventuallyEq hδ _ (hlow u hu)).fderiv_eq]
  exact ginibre_squareRootCenter_noise_coordinate hn α α.coe_nonneg _
    (hδ.trans (hlow u hu)) e i

theorem ginibreCenterRegularizedIto_positive_start_increment
    {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0) (δ : ℝ) (hδ : 0 < δ)
    (X : ℝ≥0 → Configuration n) (z : Configuration n)
    (J : ℝ≥0 → ℝ) (a t : ℝ≥0) (hat : a ≤ t)
    (hfree : ∀ u ∈ Icc a t, CollisionFree (X u))
    (hlow : ∀ u ∈ Icc a t, δ < ginibreCenterSquared n (X u))
    (hIa : IntervalIntegrable (fun r : ℝ => ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) volume 0 a)
    (hIt : IntervalIntegrable (fun r : ℝ => ginibreRealPaperSpeedGenerator n α
      (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) volume a t)
    (ha : ginibreCenterSquareRootRegularized n δ (X a) -
      ginibreCenterSquareRootRegularized n δ z = J a +
        ∫ r in (0 : ℝ)..a, ginibreRealPaperSpeedGenerator n α
          (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal))
    (ht : ginibreCenterSquareRootRegularized n δ (X t) -
      ginibreCenterSquareRootRegularized n δ z = J t +
        ∫ r in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α
          (ginibreCenterSquareRootRegularized n δ) (X r.toNNReal)) :
    ginibreSquareRootCenter n (X t)-ginibreSquareRootCenter n (X a) =
      J t-J a + ∫ r in (a : ℝ)..t, ginibreLampertiCenterDrift n α
        (ginibreCenterSquared n (X r.toNNReal)) := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals hIa hIt
  have hea := ginibreCenterSquareRootRegularized_eq hδ (X a) (hlow a ⟨le_rfl, hat⟩).le
  have het := ginibreCenterSquareRootRegularized_eq hδ (X t) (hlow t ⟨hat, le_rfl⟩).le
  have he := ginibreCenterRegularized_generator_interval hn α δ hδ X a t hat hfree hlow
  rw [hea] at ha
  rw [het] at ht
  rw [← he]
  linarith

#print axioms ginibreCenterRegularizedIto_positive_start_increment

#print axioms ginibreCenterRegularized_generator_interval
#print axioms ginibreCenterRegularized_noise_coordinate_interval
end
end GinibrePoincare
