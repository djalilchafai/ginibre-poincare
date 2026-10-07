module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltCanonicalMap

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
local instance normalizedFiniteNoiseMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0:ℝ) (T:ℝ),Configuration n) := borel _
local instance normalizedFiniteNoiseBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0:ℝ) (T:ℝ),Configuration n) := ⟨rfl⟩

def ginibreFiniteContinuousNoiseNormalize {Ω : Type*} (n : ℕ) (T : ℝ≥0)
    (N : Ω → Icc (0:ℝ) (T:ℝ) → Configuration n) (ω : Ω) :
    C(Icc (0:ℝ) (T:ℝ),Configuration n) := ContinuousMap.mkD (N ω) 0

/-- Normalization of actual almost surely continuous finite-noise paths
preserves their law across the original and tilted probability spaces.
This is a reusable measurable-mapping lemma. -/
theorem ginibreFiniteContinuousNoiseNormalize_law {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (T : ℝ≥0) (P Q : Measure Ω) [P.IsComplete]
    (N M : Ω → Icc (0:ℝ) (T:ℝ) → Configuration n)
    (hN : Measurable N) (hM : Measurable M)
    (hcN : ∀ᵐ ω ∂P, Continuous (N ω)) (hcM : ∀ᵐ ω ∂P, Continuous (M ω))
    (hQP : Q ≪ P) (hLaw : Q.map N=P.map M) :
    Measurable (ginibreFiniteContinuousNoiseNormalize n T N) ∧
      Measurable (ginibreFiniteContinuousNoiseNormalize n T M) ∧
      Q.map (ginibreFiniteContinuousNoiseNormalize n T N)=
        P.map (ginibreFiniteContinuousNoiseNormalize n T M) := by
  letI : Nonempty (Icc (0:ℝ) (T:ℝ)) := ⟨⟨0,⟨le_rfl,T.property⟩⟩⟩
  let X := ginibreFiniteContinuousNoiseNormalize n T N
  let Y := ginibreFiniteContinuousNoiseNormalize n T M
  have hXN : ∀ᵐ ω ∂P, ∀ t, X ω t=N ω t := by
    filter_upwards [hcN] with ω hω
    intro t
    simp [X,ginibreFiniteContinuousNoiseNormalize,ContinuousMap.mkD,hω]
  have hYM : ∀ᵐ ω ∂P, ∀ t, Y ω t=M ω t := by
    filter_upwards [hcM] with ω hω
    intro t
    simp [Y,ginibreFiniteContinuousNoiseNormalize,ContinuousMap.mkD,hω]
  have hXm : Measurable X := by
    apply ginibre_measurable_continuousMap_of_evaluations
    intro t
    apply (aemeasurable_iff_measurable (μ := P)).mp
    exact ((measurable_pi_apply t).comp hN).aemeasurable.congr
      (hXN.mono (fun ω hω => (hω t).symm))
  have hYm : Measurable Y := by
    apply ginibre_measurable_continuousMap_of_evaluations
    intro t
    apply (aemeasurable_iff_measurable (μ := P)).mp
    exact ((measurable_pi_apply t).comp hM).aemeasurable.congr
      (hYM.mono (fun ω hω => (hω t).symm))
  refine ⟨hXm,hYm,?_⟩
  apply actualContinuousMap_law_eq_of_raw_path_law Q P X Y hXm hYm
  have hXNQ : ∀ᵐ ω ∂Q, ∀ t, X ω t=N ω t := hQP.ae_le hXN
  have hXQ : (fun ω t => X ω t)=ᵐ[Q] N :=
    hXNQ.mono (fun ω hω => funext hω)
  have hYP : (fun ω t => Y ω t)=ᵐ[P] M := hYM.mono (fun ω hω => funext hω)
  exact (Measure.map_congr hXQ).trans (hLaw.trans (Measure.map_congr hYP).symm)

end
end GinibrePoincare
