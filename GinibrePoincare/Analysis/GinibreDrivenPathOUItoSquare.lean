module

public import GinibrePoincare.Analysis.GinibreDrivenPathDriftLeftSums
public import GinibrePoincare.Analysis.GinibreDrivenPathOUQuadraticVariation
public import GinibrePoincare.Analysis.GinibreStochasticBrownianItoSquare

@[expose] public section

/-! Actual OU square calculus through compensated left sums, without an Itô certificate. -/
open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem drivenOUPath_compensated_square_leftSums (κ x : ℝ) (N : ℝ → ℝ)
    (hN : Continuous N) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => (∑ i ∈ Finset.range (n+1),
      drivenOUPath κ x N (ginibreUniformTime t n i)*
      (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i)))+
      (∑ i ∈ Finset.range (n+1),
        (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i))^2)/2)
      atTop (𝓝 (((drivenOUPath κ x N t)^2-(drivenOUPath κ x N 0)^2)/2+
        κ*(∫ s in (0 : ℝ)..t, (drivenOUPath κ x N s)^2))) := by
  let X := drivenOUPath κ x N
  let A := drivenOUCorrection κ x N
  have hX : Continuous X := drivenOUPath_continuous κ x N hN
  have hD := ginibreUniformDriftLeftSum_tendsto_integral A (fun s => -κ*X s) X
    (fun s => by simpa only [smul_eq_mul] using drivenOUCorrection_hasDerivAt κ x N hN s)
    (continuous_const.mul hX) hX t ht
  have hI : (∫ s in (0 : ℝ)..t, X s*(-κ*X s)) = -κ*(∫ s in (0 : ℝ)..t, (X s)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hI] at hD
  have hQ := drivenOUPath_quadratic_variation_noise κ x N hN t ht
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ((X t)^2-(X 0)^2)/2) atTop
    (𝓝 (((X t)^2-(X 0)^2)/2))).sub hD).sub (hQ.div_const 2)
  have hlim : ((X t)^2-(X 0)^2)/2-(-κ*(∫ s in (0 : ℝ)..t, (X s)^2))-0/2 =
      ((X t)^2-(X 0)^2)/2+κ*(∫ s in (0 : ℝ)..t, (X s)^2) := by ring
  rw [hlim] at h
  convert h using 1
  funext n
  have hid := ginibre_finite_square_increment_identity (fun i => X (ginibreUniformTime t n i)) (n+1)
  simp only [ginibreUniformTime_end, ginibreUniformTime_zero] at hid
  have hs : (∑ i ∈ Finset.range (n+1), X (ginibreUniformTime t n i)*
      (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i)))+
      (∑ i ∈ Finset.range (n+1), X (ginibreUniformTime t n i)*
        (A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))) =
      ∑ i ∈ Finset.range (n+1), X (ginibreUniformTime t n i)*
        (X (ginibreUniformTime t n (i+1))-X (ginibreUniformTime t n i)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [X, A, drivenOUPath]
    ring
  dsimp only [X] at hid hs ⊢
  linarith

 theorem ginibreBrownianOU_compensated_square_leftSums {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (κ σ x t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (∑ i ∈ Finset.range (n+1),
      ginibreBrownianOU B κ σ x (ginibreUniformTime t n i) ω*
      (ginibreBrownianNoise B σ ω (ginibreUniformTime t n (i+1))-
        ginibreBrownianNoise B σ ω (ginibreUniformTime t n i)))+
      (∑ i ∈ Finset.range (n+1),
        (ginibreBrownianNoise B σ ω (ginibreUniformTime t n (i+1))-
          ginibreBrownianNoise B σ ω (ginibreUniformTime t n i))^2)/2)
      atTop (𝓝 (((ginibreBrownianOU B κ σ x t ω)^2-x^2)/2+
        κ*(∫ s in (0 : ℝ)..t, (ginibreBrownianOU B κ σ x s ω)^2))) := by
  filter_upwards [hB.cont, hB.eval_zero_ae_eq_zero] with ω hc hz
  have h := drivenOUPath_compensated_square_leftSums κ x (ginibreBrownianNoise B σ ω)
    (continuous_const.mul (hc.comp continuous_real_toNNReal)) t ht
  simpa only [ginibreBrownianOU, drivenOUPath, ginibreBrownianNoise, Real.toNNReal_zero,
    hz, mul_zero, drivenOUCorrection_zero, zero_add] using h

end
end GinibrePoincare
