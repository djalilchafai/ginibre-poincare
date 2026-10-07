module

public import GinibrePoincare.Analysis.BrownianOrthogonalEquilibriumPaths

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance (n : ℕ) : MeasurableSpace C(ℝ,Configuration n) := borel _
local instance (n : ℕ) : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
local instance : MeasurableSpace C(ℝ,ℂ) := borel _
local instance : BorelSpace C(ℝ,ℂ) := ⟨rfl⟩

/-- Almost sure center factorization for the actual equilibrium-initialized path. -/
theorem ginibre_equilibrium_path_center {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun p : Configuration n × Ω => ginibrePathCenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      =ᵐ[(ginibreMeasure n).prod P]
      (fun p => ginibreOUPathElement n α
        (coordinateSum p.1,ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α p.2))) := by
  classical
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hS := (ginibrePathCenter_measurable n).comp
    (ginibreEquilibriumPath_measurable hn α z₀ hz₀ B P hB)
  have hU := (ginibreOUPathElement_measurable n α).comp
    (((measurable_coordinateSum n).comp measurable_fst).prodMk
      (((ginibreContinuousNoiseCenter_continuous n).measurable.comp
        (ginibreBrownianFullContinuousNoise_measurable n B P hB α)).comp measurable_snd))
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hS hU)).mpr
  filter_upwards [ginibre_ae_collisionFree n hn] with z hz
  have hv : ginibreFreeInitialVersion z₀ hz₀ z = ⟨z,hz⟩ := by
    simp [ginibreFreeInitialVersion,hz]
  simpa only [Function.comp_def,ginibreEquilibriumPath,hv] using
    ginibreBrownian_global_path_center hn α z hz B P hB hind

/-- Almost sure relative factorization for the actual equilibrium-initialized path. -/
theorem ginibre_equilibrium_path_recenter {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    (fun p : Configuration n × Ω => ginibrePathRecenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      =ᵐ[(ginibreMeasure n).prod P] ginibreRelativeEquilibriumPath α z₀ hz₀ B := by
  classical
  letI := ginibreMeasure_isProbabilityMeasure hn
  have hS := (ginibrePathRecenter_measurable n).comp
    (ginibreEquilibriumPath_measurable hn α z₀ hz₀ B P hB)
  have hU := ginibreRelativeEquilibriumPath_measurable hn α z₀ hz₀ B P hB
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun hS hU)).mpr
  filter_upwards [ginibre_ae_collisionFree n hn] with z hz
  have hv : ginibreFreeInitialVersion z₀ hz₀ z = ⟨z,hz⟩ := by
    simp [ginibreFreeInitialVersion,hz]
  have hw : ginibreFreeInitialVersion (recenteredConfiguration n z₀) (collisionFree_recentered hz₀)
      (recenteredConfiguration n z) = ⟨recenteredConfiguration n z,collisionFree_recentered hz⟩ := by
    simp [ginibreFreeInitialVersion,collisionFree_recentered hz]
  simpa only [Function.comp_def,ginibreEquilibriumPath,ginibreRelativeEquilibriumPath,hv,hw] using
    ginibreBrownian_global_path_recenter hn α z hz B P hB hind

/-- Independence of the entire center and relative paths initialized from the
 actual Ginibre measure and driven by the original independent Brownian family. -/
theorem ginibre_equilibrium_center_relative_paths_independent {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ≥0) (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IndepFun (fun p : Configuration n × Ω => ginibrePathCenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      (fun p => ginibrePathRecenter n (ginibreEquilibriumPath α z₀ hz₀ B p))
      ((ginibreMeasure n).prod P) :=
  (ginibre_equilibrium_OU_relative_functionals_independent hn α z₀ hz₀ B P hB hind).congr
    (ginibre_equilibrium_path_center hn α z₀ hz₀ B P hB hind).symm
    (ginibre_equilibrium_path_recenter hn α z₀ hz₀ B P hB hind).symm

end
end GinibrePoincare
