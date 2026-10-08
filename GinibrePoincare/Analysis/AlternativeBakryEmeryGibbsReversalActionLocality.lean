module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalSurvival
public import GinibrePoincare.Analysis.GinibreHamiltonianOUActionLocality
@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem bakryEmeryGibbs_gradient_action_congr {E : Type*} (T : ℝ) (hT : 0 ≤ T)
    (V A : E → ℝ) (x y : ℝ → E) (hxy : EqOn x y (Icc 0 T)) :
    gradientPathReversalWeight T V A x = gradientPathReversalWeight T V A y := by
  have hi : (∫ s in (0 : ℝ)..T, A (x s)) = ∫ s in (0 : ℝ)..T, A (y s) :=
    intervalIntegral.integral_congr (fun s hs => congrArg A (hxy (by simpa [uIcc_of_le hT] using hs)))
  simp only [gradientPathReversalWeight,
    hxy (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl,hT⟩),
    hxy (show T ∈ Icc 0 T from ⟨hT,le_rfl⟩), hi]

theorem bakryEmeryGibbsOUAction_of_agrees {n : ℕ} (W : Configuration n → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T,Configuration n))
    (y : ℝ → Configuration n) (hy : ∀ s (hs : s ∈ Icc 0 T), y s = x ⟨s,hs⟩) :
    bakryEmeryGibbsOUAction W T hT x = gradientPathReversalWeight T
      (bakryEmeryGibbsRelativePotential W) (bakryEmeryGibbsOUActionIntegrand W) y := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  have he : EqOn (ContinuousMap.IccExtendCM x) y (Icc 0 T) := by
    intro s hs
    rw [hy s hs, ContinuousMap.IccExtendCM_of_mem hs]
  exact bakryEmeryGibbs_gradient_action_congr T hT _ _ _ _ he

theorem bakryEmeryGibbsOUReference_action_of_prefix {Ω : Type*} {n : ℕ}
    (W : Configuration n → ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (sample : Ω)
    (Y : ℝ≥0 → Ω → Configuration n)
    (hY : ∀ t ≤ T, Y t sample = ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample) :
    bakryEmeryGibbsOUAction W T T.property
      (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T sample) =
      gradientPathReversalWeight T (bakryEmeryGibbsRelativePotential W)
        (bakryEmeryGibbsOUActionIntegrand W) (fun s => Y s.toNNReal sample) := by
  apply bakryEmeryGibbsOUAction_of_agrees
  intro s hs
  exact hY s.toNNReal (by simpa using Real.toNNReal_le_toNNReal hs.2)

#print axioms bakryEmeryGibbs_gradient_action_congr
#print axioms bakryEmeryGibbsOUAction_of_agrees
#print axioms bakryEmeryGibbsOUReference_action_of_prefix
end
end GinibrePoincare
