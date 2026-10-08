module
public import GinibrePoincare.Analysis.CorrespondenceDynamicsStoppingFinite
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Shift a continuous noise path, retaining its zero extension to negative times. -/
def correspondenceNoiseShift (n : ℕ) (s : ℝ≥0) (N : GinibreContinuousNoise n) :
    GinibreContinuousNoise n :=
  ⟨⟨fun t => N.val ((s : ℝ) + max t 0) - N.val s,
    (N.val.continuous.comp (continuous_const.add (continuous_id.max continuous_const))).sub
      continuous_const⟩, by simp⟩

theorem correspondenceNoiseShift_continuous (n : ℕ) :
    Continuous (fun p : ℝ≥0 × GinibreContinuousNoise n => correspondenceNoiseShift n p.1 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hN : Continuous (fun p : (ℝ≥0 × GinibreContinuousNoise n) × ℝ => p.1.2.val) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  have hs : Continuous (fun p : (ℝ≥0 × GinibreContinuousNoise n) × ℝ => (p.1.1 : ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  exact (continuous_eval.comp (hN.prodMk (hs.add (continuous_snd.max continuous_const)))).sub
    (continuous_eval.comp (hN.prodMk hs))

theorem correspondenceNoiseShift_actual {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (α : ℝ) (s : ℝ≥0) :
    (fun ω => correspondenceNoiseShift n s (ginibreBrownianFullContinuousNoise n B α ω)) =ᵐ[P]
      ginibreBrownianFullContinuousNoise n (brownianFamilyShift B s) α := by
  have hshift := (brownianFamilyShift_isBrownian_independent B P hB hind s).1
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α,
    ginibreBrownianFullContinuousNoise_ae n _ P hshift α] with ω hN hS
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  change (ginibreBrownianFullContinuousNoise n B α ω).val ((s : ℝ)+max t 0) -
    (ginibreBrownianFullContinuousNoise n B α ω).val s = _
  rw [hN, hN, hS]
  have hh := ginibreConfigurationBrownianNoise_shift_nonneg n B α s ω (max t 0) (le_max_right _ _)
  rw [← hh]
  change (fun j => Real.sqrt (2*α/(n : ℝ)^2) •
      ((brownianFamilyShift B s (j,0) (max t 0).toNNReal ω : ℂ) + Complex.I *
        (brownianFamilyShift B s (j,1) (max t 0).toNNReal ω : ℂ))) = _
  have ht : (max t 0).toNNReal = t.toNNReal := by
    apply Subtype.ext
    simp [Real.toNNReal, max_assoc]
  rw [ht]
  rfl

#print axioms correspondenceNoiseShift_actual
#print axioms correspondenceNoiseShift_continuous
end
end GinibrePoincare
