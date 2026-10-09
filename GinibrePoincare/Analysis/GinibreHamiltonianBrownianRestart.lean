module

public import GinibrePoincare.Analysis.GinibreHamiltonianCanonicalRestart
public import GinibrePoincare.Analysis.GinibreStochasticNoncollision
public import GinibrePoincare.Analysis.BrownianOrthogonalFutureContinuousNoise

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem ginibreConfigurationBrownianNoise_shift_nonneg {Ω : Type*} (n : ℕ)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (α : ℝ) (s : ℝ≥0) (ω : Ω)
    (t : ℝ) (ht : 0 ≤ t) :
    ginibreConfigurationBrownianNoise n (brownianFamilyShift B s) α ω t =
      ginibreConfigurationBrownianNoise n B α ω (s+t)-ginibreConfigurationBrownianNoise n B α ω s := by
  have hc : (s : ℝ)+t=((s+t.toNNReal : ℝ≥0) : ℝ) := by simp [Real.coe_toNNReal t ht]
  funext j
  simp only [ginibreConfigurationBrownianNoise, brownianFamilyShift, hc, Real.toNNReal_coe, Pi.sub_apply]
  simp only [Complex.ofReal_sub, ← smul_sub]
  congr 1
  ring

theorem ginibreBrownianMaximalProcess_canonical_restart
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s : ℝ≥0) :
    ∀ᵐ ω ∂P,
      ginibreDrivenMaximalLifetime n α
        (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω).val
        (ginibreBrownianMaximalProcess n α z B s ω) = ⊤ ∧
      ∀ t : ℝ≥0, ginibreDrivenMaximalValue n α
        (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω).val
        (ginibreBrownianMaximalProcess n α z B s ω) t =
          ginibreBrownianMaximalProcess n α z B (s+t) ω := by
  have hBs := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  filter_upwards [(ginibreBrownianMaximalProcess_global_original_solution hn α z hz B P hB hind).2,
    ginibreBrownianFullContinuousNoise_ae n (brownianFamilyShift B s) P hBs α] with ω hω hNoise
  let X : ℝ → Configuration n := fun t => ginibreBrownianMaximalProcess n α z B t.toNNReal ω
  let N := (ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α ω).val
  have he : IsGinibreDrivenPath n α N (fun t => X (s+t)) := by
    have hShift := ginibreDrivenPath_shift n α _ _ hω.2.2.2 s s.property
    refine ⟨hShift.1,?_⟩
    intro t ht
    rw [hNoise t, ginibreConfigurationBrownianNoise_shift_nonneg n B α s ω t ht]
    exact hShift.2 t ht
  have h := ginibreDrivenPath_canonical_global
    (hω.1.comp (continuous_const.add continuous_id))
    (fun t ht => hω.2.2.1 (s+t) (add_nonneg s.property ht)) he
  simpa only [X, Function.comp_def, Pi.add_apply, id_eq, add_zero, Real.toNNReal_coe,
    ← NNReal.coe_add] using h

end
end GinibrePoincare
