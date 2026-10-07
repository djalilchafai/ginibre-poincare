module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralHorizon
public import GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import GinibrePoincare.Analysis.FiniteDimensionalItoConvergenceInMeasure

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def brownianVectorTimeEnergy {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∫ s in (0:ℝ)..(T:ℝ), ∑ i, (F i (Real.toNNReal s) ω)^2

def brownianVectorTimeEnergyUniformSum {Ω ι : Type*} [Fintype ι]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k : Fin (n+1), (∑ i, (F i (ginibreUniformBrownianTime T n k) ω)^2)*
    ((T:ℝ)/((n:ℝ)+1))

/-- Actual vector energy Riemann sums converge almost surely to the time integral. -/
theorem brownianVectorTimeEnergyUniformSum_tendsto_ae {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω)
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Icc 0 T)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => brownianVectorTimeEnergyUniformSum F T n ω)
      atTop (𝓝 (brownianVectorTimeEnergy F T ω)) := by
  have hall : ∀ᵐ ω ∂P, ∀ i, ContinuousOn (fun s => F i s ω) (Icc 0 T) := ae_all_iff.mpr hc
  filter_upwards [hall] with ω hω
  have hfi (i : ι) : ContinuousOn (fun s : ℝ => F i (Real.toNNReal s) ω) (Icc 0 (T:ℝ)) :=
    (hω i).comp continuous_real_toNNReal.continuousOn (by
      intro s hs
      constructor
      · positivity
      · simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2)
  have he : ContinuousOn (fun s : ℝ => ∑ i, (F i (Real.toNNReal s) ω)^2) (Icc 0 (T:ℝ)) :=
    continuousOn_finset_sum Finset.univ fun i _ => (hfi i).pow 2
  have ht := itoContinuousScalarRiemann_fin_tendsto
    (fun s : ℝ => ∑ i, (F i (Real.toNNReal s) ω)^2) T he
  simpa only [Real.toNNReal_coe,brownianVectorTimeEnergyUniformSum,brownianVectorTimeEnergy] using ht

theorem brownianVectorTimeEnergyUniformSum_measurable {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ i t, Measurable (F i t)) (n : ℕ) :
    Measurable (brownianVectorTimeEnergyUniformSum F T n) := by
  classical
  unfold brownianVectorTimeEnergyUniformSum
  apply Finset.measurable_sum
  intro k hk
  apply Measurable.mul_const
  apply Finset.measurable_sum
  intro i hi
  exact (hm i _).pow_const 2

/-- Energy convergence in probability is derived from actual path continuity. -/
theorem brownianVectorTimeEnergyUniformSum_tendstoInMeasure {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (P : Measure Ω) [IsFiniteMeasure P]
    (F : ι → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hm : ∀ i t, Measurable (F i t))
    (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun s => F i s ω) (Icc 0 T)) :
    TendstoInMeasure P (brownianVectorTimeEnergyUniformSum F T) atTop
      (brownianVectorTimeEnergy F T) :=
  tendstoInMeasure_of_tendsto_ae
    (fun n => (brownianVectorTimeEnergyUniformSum_measurable F T hm n).aestronglyMeasurable)
    (brownianVectorTimeEnergyUniformSum_tendsto_ae P F T hc)

end
end GinibrePoincare
