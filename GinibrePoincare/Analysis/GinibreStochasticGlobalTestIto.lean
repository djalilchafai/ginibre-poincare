module

public import GinibrePoincare.Analysis.GinibreStochasticLocalizationExhaustion
public import GinibrePoincare.Analysis.GinibreStochasticLocalTestItoIntegral

@[expose] public section

/-! # Local Itô decomposition along the global solution

A real test `f` needs only to be C² on the collision-free set. The theorem
provides increasing, exhausting Hamiltonian stops and, for each stop, a
continuous square-integrable martingale whose compensator is the concrete
paper-speed generator applied to `f`.

After obtaining the stopped Itô integral from
`GinibreStochasticLocalTestItoIntegral`, the proof removes the stopped-process
notation before the stop. At the endpoint this uses `min t τ = t`; inside the
drift integral it uses `s.toNNReal ≤ t ≤ τ` for `s` in the integration interval.
There is no claim here that the unlocalized martingale is globally integrable. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000

theorem ginibreBrownianMaximalProcess_global_local_ito
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n → ℝ) (hf : ContDiffOn ℝ 2 f {x | CollisionFree x}) :
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    let τ := fun k : ℕ => ginibreBrownianHamiltonianBoundedStop n α z B (ginibreHamiltonian n z+k) k
    (∀ k, IsStoppingTime F (fun ω => (τ k ω : WithTop ℝ≥0))) ∧
    (∀ ω, Monotone (fun k => τ k ω)) ∧
    (∀ᵐ ω ∂P, ∀ b : ℝ≥0, ∀ᶠ k : ℕ in atTop, b ≤ τ k ω) ∧
    ∀ k : ℕ, ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J F P ∧ (∀ ω, Continuous (fun t => J t ω)) ∧
      (∀ t, MemLp (J t) 2 P) ∧ J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ τ k ω,
        f (ginibreBrownianMaximalProcess n α z B t ω)-f z = J t ω+
          ∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α f
            (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)) := by
  classical
  dsimp only
  have hR (k : ℕ) : ginibreHamiltonian n z ≤ ginibreHamiltonian n z+k :=
    le_add_of_nonneg_right (Nat.cast_nonneg k)
  refine ⟨fun k => ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB _ (hR k) k,
    fun ω => ginibreBrownianHamiltonianBoundedStop_natural_monotone n α z B ω,
    ginibreBrownianHamiltonianBoundedStop_exhausts_ae hn α z hz B P hB hind, ?_⟩
  intro k
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLimit, hIto, hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_integral_exists hn α z hz B P hB hind
      (ginibreHamiltonian n z+k) (hR k) k f hf
  refine ⟨J, hJM, hJC, hJL, hJ0, ?_⟩
  filter_upwards [hIto] with ω hω
  intro t ht
  have hh := hω t ht
  have hXt : ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k t ω =
      ginibreBrownianMaximalProcess n α z B t ω := by
    change ginibreBrownianMaximalProcess n α z B (min t _) ω = _
    rw [min_eq_left ht]
  have hInt : (∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α f
        (ginibreBrownianHamiltonianStoppedProcess n α z B (ginibreHamiltonian n z+k) k s.toNNReal ω)) =
      ∫ s in (0 : ℝ)..t, ginibreRealPaperSpeedGenerator n α f
        (ginibreBrownianMaximalProcess n α z B s.toNNReal ω) := by
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le t.coe_nonneg] at hs
    have hst : s.toNNReal ≤ t := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hs.1]
      exact hs.2
    change ginibreRealPaperSpeedGenerator n α f
      (ginibreBrownianMaximalProcess n α z B (min s.toNNReal _) ω) = _
    rw [min_eq_left (hst.trans ht)]
  rw [hXt, hInt] at hh
  exact hh
end
end GinibrePoincare
