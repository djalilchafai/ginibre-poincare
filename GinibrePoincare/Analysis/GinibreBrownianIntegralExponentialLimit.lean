module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralExponentialApproximation
public import GinibrePoincare.Analysis.BrownianIntegralGaussianShiftedLimit
public import GinibrePoincare.Analysis.BrownianIntegralGirsanovVectorDensityLimit

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def brownianVectorExponentialUniformSum {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp ((∑ i, brownianUniformLeftSum (B i) (F i) T (n+1) ω)-
    brownianVectorTimeEnergyUniformSum F T n ω/2)

def brownianVectorExponentialIntegralDensity {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (I : ι → Ω → ℝ) (ω : Ω) : ℝ :=
  Real.exp ((∑ i, I i ω)-brownianVectorTimeEnergy F T ω/2)

/-- Actual stochastic integral limits and genuine energy Riemann convergence
 imply convergence in probability of the literal exponential density. -/
theorem brownianVectorExponentialUniformSum_tendstoInMeasure {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsFiniteMeasure P]
    (B : ι → ℝ≥0 → Ω → ℝ) (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ i t, Measurable (F i t))
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Set.Icc 0 T))
    (hs : ∀ i n, AEStronglyMeasurable (brownianUniformLeftSum (B i) (F i) T (n+1)) P)
    (I : ι → Ω → ℝ)
    (hI : ∀ i, TendstoInMeasure P
      (fun n => brownianUniformLeftSum (B i) (F i) T (n+1)) atTop (I i)) :
    TendstoInMeasure P (brownianVectorExponentialUniformSum B F T) atTop
      (brownianVectorExponentialIntegralDensity F T I) := by
  have he := brownianVectorTimeEnergyUniformSum_tendstoInMeasure P F T hm hc
  have hemi (n : ℕ) : AEStronglyMeasurable (brownianVectorTimeEnergyUniformSum F T n) P := (brownianVectorTimeEnergyUniformSum_measurable F T hm n).aestronglyMeasurable
  have hehalf := itoTendstoInMeasure_continuous P _ _ hemi he (fun x => x/2) (by fun_prop)
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ _ _ hs hI
  have hsumm (n : ℕ) : AEStronglyMeasurable
      (fun ω => ∑ i, brownianUniformLeftSum (B i) (F i) T (n+1) ω) P := by
    convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hs i n) using 1
    funext ω
    exact (Finset.sum_apply ω Finset.univ _).symm
  have hhalf (n : ℕ) : AEStronglyMeasurable (fun ω => brownianVectorTimeEnergyUniformSum F T n ω/2) P := by
    convert (hemi n).mul (aestronglyMeasurable_const (b := (2 : ℝ)⁻¹)) using 1
    funext ω
    simp only [Pi.mul_apply, div_eq_mul_inv]
  have hexponent := actualTendstoInMeasure_sub P _ _ _ _ hsumm hhalf hsum hehalf
  have hexponentm (n : ℕ) : AEStronglyMeasurable (fun ω => (∑ i, brownianUniformLeftSum (B i) (F i) T (n+1) ω)-brownianVectorTimeEnergyUniformSum F T n ω/2) P := (hsumm n).sub (hhalf n)
  exact itoTendstoInMeasure_continuous P _ _ hexponentm hexponent Real.exp Real.continuous_exp

end
end GinibrePoincare
