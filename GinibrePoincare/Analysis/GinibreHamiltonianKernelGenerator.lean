module

public import GinibrePoincare.Analysis.GinibreHamiltonianCoreTestExpectation
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem ginibreBrownian_core_test_infinitesimal_generator
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Tendsto (fun t : ℝ => ((∫ ω, f (ginibreBrownianMaximalProcess n α z B t.toNNReal ω) ∂P)-f z)/t)
      (𝓝[>] 0) (𝓝 (ginibreRealPaperSpeedGenerator n α f z)) := by
  let L := ginibreRealPaperSpeedGenerator n α f
  let X := fun (t : ℝ) ω => ginibreBrownianMaximalProcess n α z B t.toNNReal ω
  let A := fun (t : ℝ) ω => t⁻¹*(∫ s in (0 : ℝ)..t, L (X s ω))
  have hLc : Continuous L := (continuous_ginibrePregenerator_of_core hf).const_mul _
  have hLcompact : HasCompactSupport L := by
    change HasCompactSupport ((fun _ => (α : ℝ)/(n : ℝ))*ginibrePregenerator n f)
    exact (hasCompactSupport_ginibrePregenerator hf.2.1).mul_left
  obtain ⟨D, hD⟩ := hLcompact.exists_bound_of_continuous hLc
  have hD0 : 0 ≤ D := (norm_nonneg _).trans (hD z)
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
  have hAm : ∀ᶠ t : ℝ in 𝓝[>] 0, AEStronglyMeasurable (A t) P := by
    filter_upwards [hpos] with t ht
    have hi := (ginibreBrownian_core_test_expectation_with_integrability hn α z hz B P hB hind t.toNNReal f hf).1
    have hc : (t.toNNReal : ℝ)=t := Real.coe_toNNReal t ht.le
    simpa only [hc] using hi.aestronglyMeasurable.const_mul t⁻¹
  have hAb : ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ᵐ ω ∂P, ‖A t ω‖ ≤ D := by
    filter_upwards [hpos] with t ht
    apply ae_of_all P
    intro ω
    have hb : ‖∫ s in (0 : ℝ)..t, L (X s ω)‖ ≤ D*|t| := by
      simpa only [sub_zero] using intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t) (fun s hs => hD (X s ω))
    calc
      ‖A t ω‖ = |t⁻¹| *‖∫ s in (0 : ℝ)..t, L (X s ω)‖ := norm_mul _ _
      _ ≤ |t⁻¹| *(D*|t|) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = D := by rw [abs_of_pos ht, abs_of_pos (inv_pos.mpr ht)]; field_simp
  have hAt : ∀ᵐ ω ∂P, Tendsto (fun t => A t ω) (𝓝[>] 0) (𝓝 (L z)) := by
    filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2] with ω hω
    have hc : Continuous (fun t : ℝ => L (X t ω)) := hLc.comp hω.1
    have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 0)
      hc.aestronglyMeasurable.stronglyMeasurableAtFilter (hc.continuousAt (x := 0))
    have h := hd.tendsto_slope_zero_right
    have hi : X 0 ω=z := by simpa only [X, Real.toNNReal_zero] using hω.2.1
    simpa only [zero_add, intervalIntegral.integral_same, sub_zero, hi, smul_eq_mul, A] using h
  have hMean := tendsto_integral_filter_of_dominated_convergence (fun _ : Ω => D)
    hAm hAb (integrable_const D) hAt
  simp only [integral_const] at hMean
  have hPuniv : P.real univ=1 := by simp [Measure.real]
  rw [hPuniv, one_smul] at hMean
  apply hMean.congr'
  filter_upwards [hpos] with t ht
  have he := ginibreBrownian_core_test_expectation hn α z hz B P hB hind t.toNNReal f hf
  have hc : (t.toNNReal : ℝ)=t := Real.coe_toNNReal t ht.le
  rw [hc] at he
  dsimp only [A]
  rw [integral_const_mul, he]
  dsimp only [L, X]
  ring

end
end GinibrePoincare
