module

public import GinibrePoincare.Analysis.BrownianStoppingExitHamiltonianLevelStopping
public import GinibrePoincare.Analysis.BrownianStoppingExitMaximalEquation
public import GinibrePoincare.Analysis.GinibreHamiltonianLevelLocalization

@[expose] public section

/-! Genuine compact Hamiltonian localization of the canonical Brownian maximal process. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

 def ginibreBrownianHamiltonianBoundedStop {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0)
    (ω : Ω) : ℝ≥0 :=
  ginibreDrivenHamiltonianBoundedStop n α (ginibreBrownianFullContinuousNoise n B α ω).val z R T

 def ginibreBrownianHamiltonianStoppedProcess {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T t : ℝ≥0)
    (ω : Ω) : Configuration n :=
  ginibreBrownianMaximalProcess n α z B (min t (ginibreBrownianHamiltonianBoundedStop n α z B R T ω)) ω

 theorem ginibreBrownianHamiltonianBoundedStop_isStoppingTime {Ω : Type*}
    [mAmbient : MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) :
    IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (fun ω => ((ginibreBrownianHamiltonianBoundedStop n α z B R T ω : ℝ≥0) : ℝ≥0∞)) := by
  have hs := (ginibreBrownianHamiltonianFirstLevel_isStoppingTime hn α z hz B P hB R hR).min_const T
  convert hs using 1
  ext ω
  exact (ginibreDrivenHamiltonianBoundedStop_coe n α _ z R T).trans (min_comm _ _)

 theorem ginibreBrownianHamiltonianStoppedProcess_range {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T t : ℝ≥0) (ω : Ω) :
    ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω ∈ ginibreHamiltonianSublevel n R :=
  ginibreDrivenHamiltonianBoundedStop_range hn α _
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous
    (ginibreBrownianFullContinuousNoise n B α ω).property z hz R hR T t

 theorem ginibreBrownianHamiltonianStoppedProcess_continuous {Ω : Type*} {n : ℕ} (hn : 0 < n)
    (α : ℝ) (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (hR : ginibreHamiltonian n z ≤ R)
    (T : ℝ≥0) (ω : Ω) :
    Continuous (fun t => ginibreBrownianHamiltonianStoppedProcess n α z B R T t ω) := by
  let N := ginibreBrownianFullContinuousNoise n B α ω
  let s := ginibreDrivenHamiltonianBoundedStop n α N.val z R T
  have hs := ginibreDrivenHamiltonianBoundedStop_lt_lifetime hn α N.val N.val.continuous N.property z hz R hR T
  have hc := (ginibreDrivenMaximalPath_segment s hs).1
  have hg : Continuous (fun t : ℝ≥0 => ((min t s : ℝ≥0) : ℝ)) :=
    NNReal.continuous_coe.comp (continuous_id.min continuous_const)
  have hh := hc.comp_continuous hg (fun t => ⟨(min t s).coe_nonneg, by
    exact_mod_cast min_le_right t s⟩)
  simpa only [ginibreBrownianHamiltonianStoppedProcess, ginibreBrownianHamiltonianBoundedStop,
    ginibreBrownianMaximalProcess, ginibreDrivenMaximalPath, Real.toNNReal_coe, Function.comp_def, s, N] using hh

end
end GinibrePoincare
