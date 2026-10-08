module
public import GinibrePoincare.Analysis.CorrespondenceGUENormalization
@[expose] public section
open MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueDoubledRegularized_weighted_integral_tendsto {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : Continuous f)
    (C : ℝ) (_hC : 0≤C) (hb : ∀x, ‖f x‖≤C) :
    Tendsto (fun k => ∫ x, Real.exp (-gueDoubledRegularizedPotential n
      (gueRegularizationScale k) x)*f x) atTop
      (nhds (∫ x, gueDoubledOrderedDensity n x*f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => gueDoubledDomination n x*C)
  · intro k
    exact ((Real.continuous_exp.comp (gueDoubledRegularizedPotential_contDiff n (gueRegularizationScale_pos k)).continuous.neg).mul hf).aestronglyMeasurable
  · exact (gueDoubledDomination_integrable hn).mul_const C
  · intro k
    filter_upwards [] with x
    rw [norm_mul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul (gueDoubledRegularized_density_bound n k x) (hb x)
      (norm_nonneg _) (le_trans (Real.exp_pos _).le (gueDoubledRegularized_density_bound n k x))
  · filter_upwards [] with x
    exact (gueDoubledRegularized_density_tendsto n x).mul tendsto_const_nhds

theorem gueDoubledRegularized_partition_tendsto {n : ℕ} (hn : 0<n) :
    Tendsto (fun k => ∫ x, Real.exp (-gueDoubledRegularizedPotential n
      (gueRegularizationScale k) x)) atTop
      (nhds (∫ x, gueDoubledOrderedDensity n x)) := by
  simpa using gueDoubledRegularized_weighted_integral_tendsto hn (fun _ => 1)
    continuous_const 1 (by norm_num) (by intro x; norm_num)


/-- Actual normalized ordered GUE expectation, including the independent auxiliary Gaussian. -/
def gueDoubledOrderedExpectation (n : ℕ)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) : ℝ :=
  (∫ x, gueDoubledOrderedDensity n x*f x)/(∫ x, gueDoubledOrderedDensity n x)

theorem gueDoubledRegularized_expectation_tendsto {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : 0≤C) (hb : ∀x, ‖f x‖≤C) :
    Tendsto (fun k => ∫ x, f x ∂bakryEmeryNormalizedGibbs volume
      (gueDoubledRegularizedPotential n (gueRegularizationScale k))) atTop
      (nhds (gueDoubledOrderedExpectation n f)) := by
  simp_rw [bakryEmeryNormalizedGibbs_integral volume _
    (gueDoubledRegularizedPotential_contDiff n (gueRegularizationScale_pos _)).continuous]
  exact (gueDoubledRegularized_weighted_integral_tendsto hn f hf C hC hb).div
    (gueDoubledRegularized_partition_tendsto hn) (ne_of_gt (gueDoubledOrdered_partition_pos hn))

#print axioms gueDoubledRegularized_expectation_tendsto

#print axioms gueDoubledRegularized_weighted_integral_tendsto
#print axioms gueDoubledRegularized_partition_tendsto
end
end GinibrePoincare
