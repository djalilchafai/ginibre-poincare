module

public import GinibrePoincare.Analysis.GinibreStochasticCIRDrivenLocal
public import GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion
public import GinibrePoincare.Analysis.GinibreStochasticRadialPath

@[expose] public section

/-! Genuine stochastic CIR realization of the original Ginibre radius.
The Brownian driver, stochastic integrals and exhausting stopping times are
all constructed from the original independent Brownian family. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 2000000

theorem ginibreBrownianMaximalProcess_CIR_realization
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    let τ := fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k
    ∃ β : ℝ≥0 → Ω → ℝ,
      IsBrownianReal β P ∧ Martingale β F P ∧ (∀ t, MemLp (β t) 2 P) ∧
      (∀ s t (Y : Ω → ℝ), @Measurable Ω ℝ (F s) _ Y →
        IndepFun Y (fun ω => β (s+t) ω-β s ω) P) ∧
      (∀ k, IsStoppingTime F (fun ω => (τ k ω : WithTop ℝ≥0))) ∧
      (∀ ω, Monotone (fun k => τ k ω)) ∧
      (∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop, b ≤ τ k ω) ∧
      (∀ᵐ ω ∂P, Continuous (fun t : ℝ≥0 => pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
        ∀ t, 0 < pairwiseRadius (ginibreBrownianMaximalProcess n α z B t ω)) ∧
      ∀ (R : ℝ), ginibreHamiltonian n z ≤ R → ∀ (T : ℝ≥0),
        let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
        let a := fun t ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X t ω))
        ∃ J : ℝ≥0 → Ω → ℝ,
          Martingale J F P ∧ (∀ ω, Continuous (fun t => J t ω)) ∧
          (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
          (∀ t ≤ T, Tendsto (fun k => ∫ ω,
            (brownianUniformLeftSum β a t (k+1) ω-J t ω)^2 ∂P) atTop (𝓝 0)) ∧
          (∀ t ≤ T, TendstoInMeasure P (fun k => brownianUniformLeftSum β a t (k+1)) atTop (J t)) ∧
          (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
            pairwiseRadius (X t ω)-pairwiseRadius z = J t ω+
              ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
                ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  classical
  let i₀ : Fin n × Fin 2 := (⟨0,by omega⟩,0)
  let e : EuclideanSpace ℝ (Fin n × Fin 2) := EuclideanSpace.single i₀ 1
  have he : ‖e‖=1 := by simp [e,PiLp.norm_single]
  obtain ⟨β,hβ,hβM,hβL,hβ0,hβLim,hβShift,hβFresh⟩ :=
    ginibreBrownianMaximalProcess_radial_Brownian_exists hn α z hz B P hB hind
  refine ⟨β,hβ,hβM,hβL,hβFresh,?_,?_,?_,?_,?_⟩
  · intro k
    exact ginibreBrownianHamiltonianBoundedStop_isStoppingTime (by omega) α z hz B P hB
      _ (le_add_of_nonneg_right (Nat.cast_nonneg k)) k
  · intro ω
    exact ginibreBrownianHamiltonianBoundedStop_natural_monotone n α z B ω
  · exact ginibreBrownianHamiltonianBoundedStop_exhausts_ae (by omega) α z hz B P hB hind
  · have hh := (ginibreBrownianMaximalProcess_radius_path_properties hn α z hz B P hB hind).2
    filter_upwards [hh] with ω hω
    exact ⟨hω.1,hω.2.1⟩
  · intro R hR T
    exact ginibreBrownianMaximalProcess_local_CIR_Brownian_integral hn α z hz B P hB hind
      e he β hβL hβLim R hR T
end
end GinibrePoincare
