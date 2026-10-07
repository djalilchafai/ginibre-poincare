module

public import GinibrePoincare.Analysis.GinibreStochasticGlobalUniqueness
public import GinibrePoincare.Analysis.GinibreStochasticTwoRadiusRealization

@[expose] public section

/-! At zero speed the actual original solution is constant, including when its
initial center is zero. The degenerate radius equations admit independent
Brownian drivers chosen from two distinct original coordinate noises. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000

theorem ginibreBrownianMaximalProcess_zero_speed_constant
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ginibreBrownianMaximalProcess n 0 z B t ω = z := by
  have hs := (ginibreBrownianMaximalProcess_global_original_solution hn 0 z hz B P hB hind).2
  filter_upwards [hs] with ω hω
  intro t
  have hh := hω.2.2.2.2 (t : ℝ) t.coe_nonneg
  have hN : ginibreConfigurationBrownianNoise n B 0 ω (t : ℝ) = 0 := by
    ext j
    simp [ginibreConfigurationBrownianNoise]
  have hd : (fun s : ℝ => ginibreLangevinDrift n 0
      (ginibreBrownianMaximalProcess n 0 z B s.toNNReal ω)) = 0 := by
    funext s
    ext j
    simp [ginibreLangevinDrift]
  have hinit : ginibreBrownianMaximalProcess n 0 z B 0 ω = z := by
    simpa only [NNReal.coe_zero] using hω.2.1
  simp only [NNReal.coe_zero,Real.toNNReal_zero,Real.toNNReal_coe] at hh
  rw [hinit,hN,hd] at hh
  change ginibreBrownianMaximalProcess n 0 z B t ω = z + 0 +
    ∫ s in (0 : ℝ)..(t : ℝ), (0 : Configuration n) at hh
  simpa using hh


/-- Both genuine radius paths are constant at zero speed; the Brownian drivers
are independent entire original-coordinate processes, with no center restriction. -/
theorem ginibreBrownian_zero_speed_independent_radius_drivers
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∃ βS βR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ginibreCenterSquared n (ginibreBrownianMaximalProcess n 0 z B t ω) = ginibreCenterSquared n z ∧
        pairwiseRadius (ginibreBrownianMaximalProcess n 0 z B t ω) = pairwiseRadius z) := by
  let j : Fin n := ⟨0,hn⟩
  refine ⟨B (j,0),B (j,1),hB _,hB _,hind.indepFun (by simp),?_⟩
  filter_upwards [ginibreBrownianMaximalProcess_zero_speed_constant hn z hz B P hB hind]
    with ω hω
  intro t
  rw [hω t]
  exact ⟨rfl,rfl⟩

theorem ginibreBrownian_zero_speed_two_radius_CIR_realization
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    ∃ βS βR : ℝ≥0 → Ω → ℝ,
      IsBrownianReal βS P ∧ IsBrownianReal βR P ∧
      IndepFun (fun ω t => βS t ω) (fun ω t => βR t ω) P ∧
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n 0 z B R T
        let aS := fun t ω => Real.sqrt ((8*(0 : ℝ)/(n : ℝ))*ginibreCenterSquared n (X t ω))
        let aR := fun t ω => Real.sqrt ((8*(0 : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
        ∃ JS JR : ℝ≥0 → Ω → ℝ,
          Martingale JS F P ∧ Martingale JR F P ∧
          (∀ ω, Continuous (fun t => JS t ω)) ∧ (∀ ω, Continuous (fun t => JR t ω)) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum βS aS t (k+1) ω-JS t ω)^2 ∂P) atTop (𝓝 0)) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum βR aR t (k+1) ω-JR t ω)^2 ∂P) atTop (𝓝 0)) ∧
          ∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n 0 z B R T ω,
            (ginibreCenterSquared n (X t ω)-ginibreCenterSquared n z = JS t ω+
              ∫ s in (0 : ℝ)..t, (4*(0 : ℝ)/(n : ℝ))*(1-ginibreCenterSquared n (X s.toNNReal ω))) ∧
            (pairwiseRadius (X t ω)-pairwiseRadius z = JR t ω+
              ∫ s in (0 : ℝ)..t, (4*(0 : ℝ)/(n : ℝ))*
                ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  let j : Fin n := ⟨0,hn⟩
  refine ⟨B (j,0),B (j,1),hB _,hB _,hind.indepFun (by simp),?_⟩
  intro R hR T
  refine ⟨(fun _ _ => 0),(fun _ _ => 0),martingale_const _ P 0,martingale_const _ P 0,
    (fun _ => continuous_const),(fun _ => continuous_const),?_,?_,?_⟩
  · intro t ht
    simp [brownianUniformLeftSum]
  · intro t ht
    simp [brownianUniformLeftSum]
  · filter_upwards [ginibreBrownianMaximalProcess_zero_speed_constant hn z hz B P hB hind]
      with ω hω
    intro t ht
    have hX : ginibreBrownianHamiltonianStoppedProcess n 0 z B R T t ω = z := by
      exact hω (min t (ginibreBrownianHamiltonianBoundedStop n 0 z B R T ω))
    simp [hX]

#print axioms ginibreBrownian_zero_speed_two_radius_CIR_realization
#print axioms ginibreBrownianMaximalProcess_zero_speed_constant
#print axioms ginibreBrownian_zero_speed_independent_radius_drivers
end
end GinibrePoincare
