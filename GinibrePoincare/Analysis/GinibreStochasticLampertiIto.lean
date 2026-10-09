module

public import GinibrePoincare.Analysis.GinibreStochasticLampertiNoiseSums
public import GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral
public import GinibrePoincare.Analysis.GinibreStochasticIntegralUntilIdentity
public import GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion

@[expose] public section

/-! Actual Lamperti identification of the constructed radial Brownian motion
with the square-root-radius test of the original global solution. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2000000

theorem ginibreBrownianMaximalProcess_local_Lamperti_identity
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (β : ℝ≥0 → Ω → ℝ)
    (hβC : ∀ᵐ ω ∂P, Continuous (fun t => β t ω))
    (hβLim : ∀ t, TendstoInMeasure P (fun k ω => ∑ i,
      brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i)
        t (k+1) ω) atTop (β t))
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
      ginibreSquareRootRadius (X t ω)-ginibreSquareRootRadius z =
        Real.sqrt (2*(α : ℝ)/(n : ℝ))*β t ω+
          ∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α ginibreSquareRootRadius (X s.toNNReal ω) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let c := Real.sqrt (2*(α : ℝ)/(n : ℝ))
  have hf : ContDiffOn ℝ 2 (ginibreSquareRootRadius : Configuration n → ℝ) {x | CollisionFree x} :=
    (ginibre_contDiffOn_squareRootRadius hn).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))
  obtain ⟨J, hJM, hJC, hJL, hJ0, hJS, hIto, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists (by omega) α z hz B P hB hind
      R hR T ginibreSquareRootRadius hf
  have heq : ∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
      J t ω=c*β t ω := by
    apply ginibreContinuous_probability_limits_eq_until P
      (ginibreConfigurationBrownianGradientSum n B α X ginibreSquareRootRadius)
      (fun t k ω => c*∑ i, brownianUniformLeftSum (B i) (fun s ω =>
        ginibreRecenteredRadialDirection n e (ginibreBrownianMaximalProcess n α z B s ω) i) t (k+1) ω)
      J (fun t ω => c*β t ω) (Eventually.of_forall hJC)
      (hβC.mono (fun ω hω => continuous_const.mul hω)) T
      (ginibreBrownianHamiltonianBoundedStop n α z B R T)
      (fun ω => ginibreDrivenHamiltonianBoundedStop_le n α _ z R T) hJS
      (fun t ht => ginibre_tendstoInMeasure_const_mul P _ _ c (hβLim t))
    intro t ht k ω hts
    exact ginibreConfigurationBrownianGradientSum_squareRootRadius_full_direction
      hn α α.coe_nonneg z hz B R hR T e t k ω hts
  filter_upwards [heq, hIto] with ω hω hItoω
  intro t ht
  rw [← hω t ht]
  exact hItoω t ht
end
end GinibrePoincare
