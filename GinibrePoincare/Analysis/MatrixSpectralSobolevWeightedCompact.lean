module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevCompactMollification

@[expose] public section

/-! # Actual weak gradient approximation under bounded Gaussian densities -/
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def weightedConfigurationCompactDirectionalPairs (m : ℕ) (I : Type*) [Fintype I]
    (v : I → Configuration m) (μ : Measure (Configuration m)) :
    Set (Lp ℝ 2 μ × (I → Lp ℝ 2 μ)) :=
  {p | ∃ f : Configuration m → ℝ, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (p.1 : Configuration m → ℝ) =ᵐ[μ] f ∧
    ∀ i, (p.2 i : Configuration m → ℝ) =ᵐ[μ] (fun x => fderiv ℝ f x (v i))}

/-- Simultaneous ordinary weak gradient approximation transfers continuously to
an actual bounded-density weighted L² graph. -/
theorem weighted_configuration_compact_weak_pair_mem_closure (m : ℕ)
    {I : Type*} [Fintype I] (v : I → Configuration m)
    (μ : Measure (Configuration m)) (c : ℝ≥0∞) (hc : c ≠ (⊤ : ℝ≥0∞))
    (hμ : μ ≤ c • (volume : Measure (Configuration m)))
    (f : Configuration m → ℝ) (g : I → Configuration m → ℝ)
    (hf : MemLp f 2 volume) (hg : ∀ i, MemLp (g i) 2 volume)
    (hfc : HasCompactSupport f) (hgc : ∀ i, HasCompactSupport (g i))
    (hw : ∀ i, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g i x * θ x) = -(∫ x, f x * fderiv ℝ θ x (v i))) :
    ((hf.of_measure_le_smul hc hμ).toLp f,
      fun i => ((hg i).of_measure_le_smul hc hμ).toLp (g i)) ∈
      closure (weightedConfigurationCompactDirectionalPairs m I v μ) := by
  let T : Lp ℝ 2 (volume : Measure (Configuration m)) →L[ℝ] Lp ℝ 2 μ :=
    Lp.LpToLpOfMeasureLeSMul hc hμ
  let Φ := fun p : Lp ℝ 2 (volume : Measure (Configuration m)) ×
      (I → Lp ℝ 2 (volume : Measure (Configuration m))) => (T p.1, fun i => T (p.2 i))
  have hΦ : Continuous Φ := by
    exact (T.continuous.comp continuous_fst).prodMk
      (continuous_pi fun i => T.continuous.comp ((continuous_apply i).comp continuous_snd))
  have hac : μ ≪ (volume : Measure (Configuration m)) :=
    Measure.absolutelyContinuous_of_le_smul hμ
  have hsub : configurationCompactDirectionalPairs m I v ⊆
      Φ ⁻¹' closure (weightedConfigurationCompactDirectionalPairs m I v μ) := by
    intro p hp
    obtain ⟨F, hF, hFc, hv, hd⟩ := hp
    apply subset_closure
    refine ⟨F, hF, hFc, ?_, ?_⟩
    · exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ p.1).trans (hac.ae_eq hv)
    · intro i
      exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ (p.2 i)).trans (hac.ae_eq (hd i))
  have hclosure := closure_minimal hsub (isClosed_closure.preimage hΦ)
    (configuration_compact_weak_pair_mem_directional_closure m v f g hf hg hfc hgc hw)
  have hT (u : Configuration m → ℝ) (hu : MemLp u 2 volume) :
      T (hu.toLp u) = (hu.of_measure_le_smul hc hμ).toLp u := by
    apply Lp.ext
    exact (Lp.coeFn_LpToLpOfMeasureLeSMul hc hμ (hu.toLp u)).trans
      ((hac.ae_eq hu.coeFn_toLp).trans (hu.of_measure_le_smul hc hμ).coeFn_toLp.symm)
  change (T (hf.toLp f), fun i => T ((hg i).toLp (g i))) ∈
    closure (weightedConfigurationCompactDirectionalPairs m I v μ) at hclosure
  simpa only [hT] using hclosure

end
end GinibrePoincare
