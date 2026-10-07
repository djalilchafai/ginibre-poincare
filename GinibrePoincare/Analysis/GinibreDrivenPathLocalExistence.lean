module

public import GinibrePoincare.Analysis.GinibreDrivenPathContinuousNoisePicard
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! # Genuine local collision-free existence for continuous additive noise -/
open Set Metric MeasureTheory
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

 theorem ginibreDrivenPath_continuous_noise_local_exists (n : ℕ) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) :
    ∃ τ > (0 : ℝ), ∃ X : ℝ → Configuration n,
      ContinuousOn X (Icc 0 τ) ∧ X 0 = z ∧
      ∀ t ∈ Icc 0 τ, CollisionFree (X t) ∧
        IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t ∧
        X t = z+N t+∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (X u) := by
  obtain ⟨Y, hY0, ε, hε, hY⟩ := ginibreDrivenPath_continuous_noise_local_correction n α z hz N hN hN0
  let X := fun t => Y t+N t
  have hX0 : X 0 = z := by simp [X, hY0, hN0]
  have hXcont : ContinuousAt X 0 := (hY 0 (by constructor <;> linarith)).continuousAt.add hN.continuousAt
  have hop : IsOpen {w : Configuration n | CollisionFree w} := by
    have he : {w : Configuration n | CollisionFree w} =
        (vandermonde : Configuration n → ℂ) ⁻¹' ({0}ᶜ : Set ℂ) := by
      ext w
      simp [← vandermonde_ne_zero_iff]
    rw [he]
    exact isClosed_singleton.isOpen_compl.preimage continuous_vandermonde
  have hev : ∀ᶠ t in nhds 0, CollisionFree (X t) := hXcont.eventually (by
    rw [hX0]
    exact hop.mem_nhds hz)
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hev
  let τ := min ε δ / 2
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hte (t : ℝ) (ht : t ∈ Icc 0 τ) : t ∈ Ioo (-ε) ε := by
    have hmin := min_le_left ε δ
    dsimp [τ] at ht
    constructor <;> linarith [ht.1, ht.2]
  have hcf (t : ℝ) (ht : t ∈ Icc 0 τ) : CollisionFree (X t) := by
    apply hδs
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    have hmin := min_le_right ε δ
    dsimp [τ] at ht
    linarith [ht.2]
  have hYon : ContinuousOn Y (Icc 0 τ) :=
    fun t ht => (hY t (hte t ht)).continuousAt.continuousWithinAt
  have hXon : ContinuousOn X (Icc 0 τ) := hYon.add hN.continuousOn
  have hb : ContinuousOn (ginibreLangevinDrift n α) {w : Configuration n | CollisionFree w} :=
    fun w hw => (ginibreLangevinDrift_contDiffAt n α w hw).continuousAt.continuousWithinAt
  have hD : ContinuousOn (fun t => ginibreLangevinDrift n α (X t)) (Icc 0 τ) :=
    hb.comp hXon hcf
  refine ⟨τ, hτ, X, hXon, hX0, ?_⟩
  intro t ht
  have hus : uIcc (0 : ℝ) t ⊆ Icc 0 τ := by
    rw [uIcc_of_le ht.1]
    exact Icc_subset_Icc_right ht.2
  have hint : IntervalIntegrable (fun u => ginibreLangevinDrift n α (X u)) volume 0 t := (hD.mono hus).intervalIntegrable
  refine ⟨hcf t ht, hint, ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun u hu => hY u (hte u (hus hu))) hint
  change Y t+N t = z+N t+_
  rw [hFTC, hY0]
  abel

end
end GinibrePoincare
