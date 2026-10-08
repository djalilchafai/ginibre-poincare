module
public import GinibrePoincare.Analysis.CorrespondenceOperatorStoppedMartingale
public import GinibrePoincare.Analysis.GinibreStochasticLocalTestIto
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- The concrete localized test-function deficit is a stopped continuous
martingale, at every time simultaneously. Both its drift and its localization
are the actual Ginibre objects. -/
theorem correspondenceOperator_local_martingale_problem
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0<n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀i,IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z≤R) (T : ℝ≥0)
    (f : Configuration n→ℝ) (hf : ContDiffOn ℝ 2 f {x | CollisionFree x}) :
    ∃ M : ℝ≥0→Ω→ℝ,
      Martingale M (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ω,Continuous (fun t => M t ω)) ∧
      (∀ᵐ ω ∂P, ∀t : ℝ≥0,
        f (ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω)-f z-
          (∫ s in (0:ℝ)..(min (ginibreBrownianHamiltonianBoundedStop n α z B R T ω) t:ℝ),
            ginibreRealPaperSpeedGenerator n α f
              (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω))=M t ω) := by
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  obtain ⟨J,hJ,hc,hLp,h0,he,hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_martingale_exists hn α z hz B P hB hind R hR T f hf
  have hσ := ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB R hR T
  refine ⟨fun t ω => J (min (σ ω) t) ω,
    correspondenceOperator_continuous_stopped_martingale hJ hc σ hσ,?_,?_⟩
  · intro ω
    exact (hc ω).comp (continuous_const.min continuous_id)
  · filter_upwards [he] with ω hω
    intro t
    have hh := hω (min (σ ω) t) (min_le_left _ _)
    have hxe : X (min (σ ω) t) ω=X t ω := by
      simp only [X,ginibreBrownianHamiltonianStoppedProcess,σ]
      congr 1
      exact min_assoc _ _ _ |>.trans (by simp [min_comm])
    change f (X (min (σ ω) t) ω)-f z=J (min (σ ω) t) ω+_ at hh
    rw [hxe] at hh
    change f (X t ω)-f z-(∫ s in (0:ℝ)..(min (σ ω) t:ℝ),
      ginibreRealPaperSpeedGenerator n α f (X s.toNNReal ω))=J (min (σ ω) t) ω
    simp only [NNReal.coe_min,X] at hh ⊢
    linarith
#print axioms correspondenceOperator_local_martingale_problem
end
end GinibrePoincare
