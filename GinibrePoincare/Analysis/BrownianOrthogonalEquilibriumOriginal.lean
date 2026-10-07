module

public import GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumFactorization

@[expose] public section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance (n : ℕ) : MeasurableSpace C(ℝ,Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ,ℂ) := borel _
local instance : BorelSpace C(ℝ,ℂ) := ⟨rfl⟩

/-- The equilibrium path version agrees at every time with the original canonical
 Brownian solution initialized from the actual Ginibre sample. -/
theorem ginibre_equilibrium_path_eq_original {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P, ∀ t : ℝ,
      ginibreEquilibriumPath α z₀ hz₀ B p t =
        ginibreBrownianMaximalProcess n α p.1 B (Real.toNNReal t) p.2 := by
  classical
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hm : Measurable (fun p : Configuration n × Ω =>
      (ginibreFreeInitialVersion z₀ hz₀ p.1,ginibreBrownianFullContinuousNoise n B α p.2)) :=
    ((ginibreFreeInitialVersion_measurable z₀ hz₀).comp measurable_fst).prodMk
      ((ginibreBrownianFullContinuousNoise_measurable n B P hB α).comp measurable_snd)
  have hL : ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P,
      ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α p.2).val
        (ginibreFreeInitialVersion z₀ hz₀ p.1).val = ⊤ := by
    apply (Measure.ae_prod_iff_ae_ae ((ginibreDriven_global_joint_measurableSet hn α).preimage hm)).mpr
    exact Eventually.of_forall fun z =>
      ginibreBrownianMaximalLifetime_top_ae hn α _ (ginibreFreeInitialVersion z₀ hz₀ z).property B P hB hind
  have hC : ∀ᵐ p : Configuration n × Ω ∂(ginibreMeasure n).prod P, CollisionFree p.1 := by
    apply (Measure.ae_prod_iff_ae_ae ((isOpen_collisionFree n).measurableSet.preimage measurable_fst)).mpr
    exact (ginibre_ae_collisionFree n hn).mono fun z hz => Eventually.of_forall fun _ => hz
  filter_upwards [hL,hC] with p hL hC
  intro t
  have hv : ginibreFreeInitialVersion z₀ hz₀ p.1 = ⟨p.1,hC⟩ := by
    simp [ginibreFreeInitialVersion,hC]
  have hL' : ginibreDrivenMaximalLifetime n α (ginibreBrownianFullContinuousNoise n B α p.2).val p.1 = ⊤ := by
    simpa only [hv] using hL
  simp only [ginibreEquilibriumPath,ginibreDrivenGlobalPathElement,hv,dif_pos hL',
    ContinuousMap.coe_mk,ginibreBrownianMaximalProcess]

/-- Actual original Brownian whole-process independence with initial law exactly
 Ginibre; no assumption of stationarity or stochastic factorization is used. -/
theorem ginibreBrownian_equilibrium_center_relative_processes_independent {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => fun t : ℝ≥0 =>
      coordinateSum (ginibreBrownianMaximalProcess n α p.1 B t p.2))
      (fun p => fun t : ℝ≥0 => recenteredConfiguration n
        (ginibreBrownianMaximalProcess n α p.1 B t p.2)) ((ginibreMeasure n).prod P) := by
  have hS : Measurable (fun X : C(ℝ,ℂ) => fun t : ℝ≥0 => X (t:ℝ)) := by
    apply measurable_pi_lambda
    intro t
    exact (continuous_eval_const (t:ℝ)).measurable
  have hW : Measurable (fun X : C(ℝ,Configuration n) => fun t : ℝ≥0 => X (t:ℝ)) := by
    apply measurable_pi_lambda
    intro t
    exact (continuous_eval_const (t:ℝ)).measurable
  have h := (ginibre_equilibrium_center_relative_paths_independent hn α z₀ hz₀ B P hB hind).comp hS hW
  apply h.congr
  · filter_upwards [ginibre_equilibrium_path_eq_original hn α z₀ hz₀ B P hB hind] with p hp
    funext t
    simpa only [Function.comp_def,ginibrePathCenter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
      coordinateSumCLM_apply,hp,Real.toNNReal_coe]
  · filter_upwards [ginibre_equilibrium_path_eq_original hn α z₀ hz₀ B P hB hind] with p hp
    funext t
    simpa only [Function.comp_def,ginibrePathRecenter,ContinuousMap.comp_apply,ContinuousMap.coe_mk,
      recenteredCLM_apply,hp,Real.toNNReal_coe]

end
end GinibrePoincare
