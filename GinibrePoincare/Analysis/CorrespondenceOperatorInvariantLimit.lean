module
public import GinibrePoincare.Analysis.CorrespondenceOperatorErgodicity
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
@[expose] public section
open MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
/-- Strong L² convergence and a uniform observable bound transfer equilibrium
integrals to every absolutely continuous probability, without any L² assumption
on its density. Only a subsequence is needed. -/
theorem correspondenceOperator_invariant_limit {n : ℕ} (hn : 0<n)
    (ρ : Measure (Configuration n)) [IsProbabilityMeasure ρ]
    (hρ : ρ ≪ ginibreMeasure n) (F : ℕ → GinibreFullValueL2 n)
    (v : ℕ → Configuration n → ℝ) (a b C : ℝ)
    (hF : Tendsto F atTop (𝓝 (ginibreRealConstantL2 n hn a)))
    (hrep : ∀k,F k=ᵐ[ginibreMeasure n]v k)
    (hv : ∀k,AEStronglyMeasurable (v k) ρ)
    (hbound : ∀k,∀ᵐz∂ρ,‖v k z‖≤C)
    (hInv : ∀k,∫z,v k z∂ρ=b) : b=a := by
  obtain ⟨ns,hns,hlim⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  have hae : ∀ᵐz∂ginibreMeasure n,
      Tendsto (fun k=>v (ns k) z) atTop (𝓝 a) := by
    filter_upwards [hlim,ae_all_iff.mpr hrep,ginibreRealConstantL2_ae n hn a]
      with z hz hr hc
    simpa only [hr,hc] using hz
  have hi : Tendsto (fun k=>∫z,v (ns k) z∂ρ) atTop (𝓝 a) := by
    have h := tendsto_integral_of_dominated_convergence (fun _ : Configuration n=>C)
      (fun k=>hv (ns k)) (integrable_const C) (fun k=>hbound (ns k)) (hρ.ae_le hae)
    simpa using h
  simp only [hInv] at hi
  exact tendsto_nhds_unique tendsto_const_nhds hi
#print axioms correspondenceOperator_invariant_limit
end
end GinibrePoincare
