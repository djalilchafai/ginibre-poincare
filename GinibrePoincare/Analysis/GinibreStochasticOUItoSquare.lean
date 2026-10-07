module

public import GinibrePoincare.Analysis.GinibreDrivenPathOUItoSquare
public import GinibrePoincare.Analysis.GinibreStochasticProbabilityOperations
public import GinibrePoincare.Analysis.GinibreStochasticOUConvolution

@[expose] public section

/-! Actual original OU stochastic square left sums converge in probability. -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def ginibreBrownianOUItoSquareLeftSum {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (rate t : ℝ≥0) (x : ℝ) (n : ℕ) : Ω → ℝ := fun ω =>
  ∑ i ∈ Finset.range (n+1), ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (ginibreUniformTime t n i) ω*
    (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n (i+1))-
      ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n i))

theorem ginibreBrownianNoise_uniform_square_sum {Ω : Type*}
    (B : ℝ≥0 → Ω → ℝ) (rate t : ℝ≥0) (n : ℕ) (ω : Ω) :
    (∑ i ∈ Finset.range (n+1),
      (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n (i+1))-
        ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n i))^2) =
      (rate : ℝ)*ginibreBrownianUniformQuadraticSum B t n ω := by
  dsimp [ginibreBrownianUniformQuadraticSum, ginibreBrownianQuadraticSum]
  rw [Fin.sum_univ_eq_sum_range (fun i =>
    (B (ginibreUniformBrownianTime t n (i+1)) ω-B (ginibreUniformBrownianTime t n i) ω)^2)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [ginibreBrownianNoise, ginibreUniformBrownianTime]
  rw [← mul_sub, mul_pow, Real.sq_sqrt rate.coe_nonneg]

theorem ginibreBrownianOUItoSquareLeftSum_tendstoInProbability {Ω : Type*}
    [MeasurableSpace Ω] (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (rate t : ℝ≥0) (x : ℝ) :
    TendstoInMeasure P (fun n => ginibreBrownianOUItoSquareLeftSum B rate t x n) atTop
      (fun ω => ((ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x t ω)^2-x^2-(rate : ℝ)*(t : ℝ))/2+
        (rate : ℝ)*(∫ s in (0 : ℝ)..t, (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω)^2)) := by
  let := hB.isGaussianProcess.isProbabilityMeasure
  let S := fun n => ginibreBrownianOUItoSquareLeftSum B rate t x n
  let Q := fun n => ginibreBrownianUniformQuadraticSum B t n
  let R := fun n ω => S n ω+(rate : ℝ)*Q n ω/2
  let Z := fun ω => ((ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x t ω)^2-x^2)/2+
    (rate : ℝ)*(∫ s in (0 : ℝ)..t, (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x s ω)^2)
  have hRae : ∀ᵐ ω ∂P, Tendsto (fun n => R n ω) atTop (𝓝 (Z ω)) := by
    have h := ginibreBrownianOU_compensated_square_leftSums B P hB rate (Real.sqrt (rate : ℝ)) x t t.coe_nonneg
    simpa only [R, S, Q, Z, ginibreBrownianOUItoSquareLeftSum, ginibreBrownianNoise_uniform_square_sum] using h
  have hSmeas (n : ℕ) : AEStronglyMeasurable (S n) P := by
    dsimp only [S, ginibreBrownianOUItoSquareLeftSum]
    have hs := Finset.aestronglyMeasurable_sum (μ := P) (Finset.range (n+1)) (f := fun i ω =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (ginibreUniformTime t n i) ω*
        (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n (i+1))-
          ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n i)))
    have he : ginibreBrownianOUItoSquareLeftSum B rate t x n =
        ∑ i ∈ Finset.range (n+1), (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (ginibreUniformTime t n i) ω*
          (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n (i+1))-
            ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω (ginibreUniformTime t n i))) := by
      funext ω
      simp only [ginibreBrownianOUItoSquareLeftSum, Finset.sum_apply]
    rw [he]
    apply hs
    intro i hi
    have hv : AEStronglyMeasurable
        (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) x (ginibreUniformTime t n i)) P := by
      simpa only [ginibreUniformBrownianTime_coe] using
        (ginibreBrownianOU_hasLaw B P hB rate (ginibreUniformBrownianTime t n i) x).aemeasurable.aestronglyMeasurable
    exact hv.mul ((hB.aemeasurable _).aestronglyMeasurable.const_mul _ |>.sub
      ((hB.aemeasurable _).aestronglyMeasurable.const_mul _))
  have hQmeas (n : ℕ) : AEStronglyMeasurable (Q n) P := by
    exact (ginibreBrownianQuadraticSum_memLp_two B P hB.toIsPreBrownianReal (n+1)
      (fun i => ginibreUniformBrownianTime t n i)
      ((ginibreUniformBrownianTime_mono t n).comp Fin.val_strictMono.monotone)).aestronglyMeasurable
  have hRm (n : ℕ) : AEStronglyMeasurable (R n) P := by
    convert (hSmeas n).add ((hQmeas n).const_mul ((rate : ℝ)/2)) using 1
    funext ω
    dsimp [R]
    ring
  have hR : TendstoInMeasure P R atTop Z := tendstoInMeasure_of_tendsto_ae hRm hRae
  have hQ := ginibre_tendstoInMeasure_const_mul P Q (fun _ => (t : ℝ)) ((rate : ℝ)/2)
    (ginibreBrownianUniformQuadraticSum_tendstoInProbability B P hB.toIsPreBrownianReal t)
  have h := ginibre_tendstoInMeasure_add P R (fun n ω => -((rate : ℝ)/2*Q n ω)) Z
    (fun _ => -((rate : ℝ)/2*(t : ℝ))) hR
    (ginibre_tendstoInMeasure_neg P _ _ hQ)
  convert h using 1
  · funext n ω
    dsimp [R, S]
    ring
  · funext ω
    dsimp [Z]
    ring

end
end GinibrePoincare
