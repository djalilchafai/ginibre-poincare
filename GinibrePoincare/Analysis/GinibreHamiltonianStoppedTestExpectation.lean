module

public import GinibrePoincare.Analysis.GinibreHamiltonianLocalizationLimit
public import GinibrePoincare.Analysis.GinibreGeneratorL2
public import GinibrePoincare.Analysis.GinibreStochasticLocalTestIto

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

theorem ginibreBrownian_stopped_core_test_expectation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) (T : ℝ≥0)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    Integrable (fun ω => ∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
      ginibreRealPaperSpeedGenerator n α f
        (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) P ∧
    (∫ ω, f (ginibreBrownianHamiltonianStoppedProcess n α z B R T T ω) ∂P) =
      f z+∫ ω, (∫ s in (0 : ℝ)..(ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ),
        ginibreRealPaperSpeedGenerator n α f
          (ginibreBrownianHamiltonianStoppedProcess n α z B R T s.toNNReal ω)) ∂P := by
  let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
  let σ := ginibreBrownianHamiltonianBoundedStop n α z B R T
  let X := ginibreBrownianHamiltonianStoppedProcess n α z B R T
  let Y := fun ω => f (X T ω)
  let A := fun ω => ∫ s in (0 : ℝ)..(σ ω : ℝ), ginibreRealPaperSpeedGenerator n α f (X s.toNNReal ω)
  have hf2 : ContDiffOn ℝ 2 f {x | CollisionFree x} :=
    (hf.1.of_le (WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffOn
  obtain ⟨J,hJM,hJC,hJL,hJ0,hEq,hEnd⟩ :=
    ginibreBrownianMaximalProcess_local_test_ito_martingale_exists hn α z hz B P hB hind R hR T f hf2
  have hσ := ginibreBrownianHamiltonianBoundedStop_isStoppingTime hn α z hz B P hB R hR T
  have hσT (ω : Ω) : σ ω ≤ T := ginibreDrivenHamiltonianBoundedStop_le n α _ z R T
  have hStop := continuous_martingale_bounded_stopping_integral hJM (ae_of_all P hJC) hσ hσT
  have hJmean : (∫ ω, J (σ ω) ω ∂P)=0 := by
    rw [hStop.2,integral_congr_ae hJ0]
    simp
  have hXmeas : Measurable (X T) :=
    ((ginibreBrownianHamiltonianStoppedProcess_stronglyAdapted hn α z hz B P hB R hR T T).mono (F.le T)).measurable
  obtain ⟨C,hC⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  have hY : Integrable Y P := (integrable_const C).mono'
    (hf.1.continuous.measurable.comp hXmeas).aestronglyMeasurable
    (ae_of_all P (fun ω => hC (X T ω)))
  have hAe : (fun ω => Y ω-f z-J (σ ω) ω) =ᵐ[P] A := hEnd.mono (fun ω h => by
    change Y ω=f z+J (σ ω) ω+A ω at h
    linarith)
  have hA : Integrable A P := ((hY.sub (integrable_const (f z))).sub hStop.1).congr hAe
  refine ⟨hA,?_⟩
  have hInt := integral_congr_ae hEnd
  change (∫ ω, Y ω ∂P)=(∫ ω, f z+J (σ ω) ω+A ω ∂P) at hInt
  rw [integral_add (f := fun ω => f z+J (σ ω) ω) (g := A)
      ((integrable_const (f z)).add hStop.1) hA,
    integral_add (f := fun _ => f z) (g := fun ω => J (σ ω) ω)
      (integrable_const (f z)) hStop.1,hJmean] at hInt
  simpa using hInt

end
end GinibrePoincare
