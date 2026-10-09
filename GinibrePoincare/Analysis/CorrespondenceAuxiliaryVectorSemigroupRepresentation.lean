module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryGeneratorVectorMeasure

@[expose] public section
open MeasureTheory Set Filter
open scoped Topology CompactlySupported NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Every vector's actual generator spectral measure represents its concrete
full symmetric diffusion semigroup. This ties the Riesz–Markov measure and
inverse-resolvent transformation to the already identified generator/evolution. -/
theorem ginibreGeneratorVectorSpectralMeasure_semigroup (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (t : ℝ≥0) :
    (∫ lam : ℝ, Real.exp ((t : ℝ)*lam) ∂ginibreGeneratorVectorSpectralMeasure n hn u) =
      (inner ℂ u (ginibreFullEvolution n hn t u)).re := by
  letI : CompleteSpace (ginibreSymmetricL2 n) := (isClosed_ginibreSymmetricL2 n).completeSpace_coe
  letI : InnerProductSpace ℂ (ginibreSymmetricL2 n) := inferInstance
  letI : CStarAlgebra (ginibreSymmetricL2 n →L[ℂ] ginibreSymmetricL2 n) := inferInstance
  let R := ginibreFullComplexResolvent n hn
  let hR := ginibreFullComplexResolvent_isSelfAdjoint n hn
  let μ := vectorSpectralMeasure R hR u
  have hmult : (∫ r : spectrum ℝ R, resolventEvolutionMultiplier (t : ℝ) r.val ∂μ) =
      (inner ℂ u (resolventCfcEvolution R t u)).re := by
    let φ : C_c(spectrum ℝ R, ℝ) :=
      ⟨⟨fun r => resolventEvolutionMultiplier (t : ℝ) r.val,
        (resolventEvolutionMultiplier_continuous _).comp continuous_subtype_val⟩,
        HasCompactSupport.of_compactSpace _⟩
    have h := integral_vectorSpectralMeasure R hR u φ
    have hc : (cfcHom hR) φ.toContinuousMap = resolventCfcEvolution R t := by
      unfold resolventCfcEvolution
      exact (cfc_apply _ R hR (resolventEvolutionMultiplier_continuous _).continuousOn).symm
    rw [hc] at h
    exact h
  unfold ginibreGeneratorVectorSpectralMeasure ginibreResolventVectorSpectralMeasure
  rw [Measure.map_map measurable_inverseResolventSpectralCoordinate measurable_subtype_coe]
  have hf : AEStronglyMeasurable (fun lam : ℝ => Real.exp ((t : ℝ)*lam))
      (Measure.map (inverseResolventSpectralCoordinate ∘ Subtype.val) μ) :=
    (show Continuous (fun lam : ℝ => Real.exp ((t : ℝ)*lam)) by fun_prop).aestronglyMeasurable
  rw [integral_map (measurable_inverseResolventSpectralCoordinate.comp
      measurable_subtype_coe).aemeasurable hf]
  change (∫ r : spectrum ℝ R, Real.exp ((t : ℝ)*inverseResolventSpectralCoordinate r.val) ∂μ) = _
  change _ = (inner ℂ u (resolventCfcEvolution R t u)).re
  rw [← hmult]
  apply integral_congr_ae
  by_cases ht : t = 0
  · subst t
    exact ae_of_all _ (fun r => by simp)
  · have htpos : 0 < (t : ℝ) := by exact_mod_cast (lt_of_le_of_ne (show (0 : ℝ≥0) ≤ t from zero_le) (Ne.symm ht))
    have hzero : ∀ᵐ r : spectrum ℝ R ∂μ, r.val ≠ 0 := by
      apply ae_iff.mpr
      simpa only [not_not] using vectorSpectralMeasure_zero_atom R hR
        (ginibreFullComplexResolvent_spectrum n hn) (ginibreFullComplexResolvent_denseRange n hn) u
    filter_upwards [hzero] with r hr
    have hnonneg := (ginibreFullComplexResolvent_spectrum n hn r.property).1
    have hrpos : 0 < r.val := lt_of_le_of_ne hnonneg (Ne.symm hr)
    rw [resolventEvolutionMultiplier_positive_formula htpos hrpos]
    congr 1
    unfold inverseResolventSpectralCoordinate
    ring

#print axioms ginibreGeneratorVectorSpectralMeasure_semigroup
end
end GinibrePoincare
