module

public import GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral
public import GinibrePoincare.Analysis.GinibreStochasticCIRNoiseSums

@[expose] public section

/-! Actual CIR radial martingale compensation with its genuinely constructed
original Brownian-integral representation, on canonical Hamiltonian stops. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

theorem ginibreBrownianMaximalProcess_local_CIR_integral_exists
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) :
    let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
    ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, TendstoInMeasure P (fun k ω => ∑ i,
        brownianUniformLeftSum (B i)
          (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X s ω))*
            ginibreRecenteredRadialDirection n e (X s ω) i) t (k+1) ω) atTop (J t)) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ ginibreBrownianHamiltonianBoundedStop n α z B R T ω,
        pairwiseRadius (X t ω)-pairwiseRadius z = J t ω+
          ∫ s in (0 : ℝ)..t, (4*(α : ℝ)/(n : ℝ))*
            ((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
  classical
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  have hf : ContDiffOn ℝ 2 (pairwiseRadius : Configuration n → ℝ) {x | CollisionFree x} :=
    ((ginibre_contDiff_pairwiseRadius n).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffOn
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLimit, hIto, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists (by omega) α z hz B P hB hind R hR T pairwiseRadius hf
  have hCF (s : ℝ≥0) (ω : Ω) : CollisionFree (X s ω) :=
    (ginibreBrownianHamiltonianStoppedProcess_range (by omega) α z hz B R hR T s ω).1
  have hSum (t : ℝ≥0) : ginibreConfigurationBrownianGradientSum n B α X pairwiseRadius t =
      (fun k ω => ∑ i, brownianUniformLeftSum (B i)
        (fun s ω => Real.sqrt ((8*(α : ℝ)/(n : ℝ))*pairwiseRadius (X s ω))*
          ginibreRecenteredRadialDirection n e (X s ω) i) t (k+1) ω) := by
    funext k ω
    exact ginibreConfigurationBrownianGradientSum_radius hn B α α.coe_nonneg X hCF e t k ω
  refine ⟨J, hJM, hJC, hJL, hJ0,?_,?_⟩
  · intro t ht
    rw [← hSum t]
    exact hLimit t ht
  · filter_upwards [hIto] with ω hω
    intro t ht
    have hh := hω t ht
    have hg : (fun s : ℝ => ginibreRealPaperSpeedGenerator n α pairwiseRadius (X s.toNNReal ω)) =
        (fun s => (4*(α : ℝ)/(n : ℝ))*((recenteredGammaShape n : ℝ)-pairwiseRadius (X s.toNNReal ω))) := by
      funext s
      exact ginibreRealPaperSpeedGenerator_pairwiseRadius hn α _ (hCF _ ω)
    rw [hg] at hh
    exact hh

end
end GinibrePoincare
