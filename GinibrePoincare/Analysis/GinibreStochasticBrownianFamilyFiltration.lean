module

public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyPast
public import Mathlib.Probability.Martingale.Basic

@[expose] public section

/-! The actual whole Brownian-family past is a filtration. -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

def ginibreBrownianFamilyPastSpace {Ω ι : Type*} (B : ι → ℝ≥0 → Ω → ℝ) (s : ℝ≥0) : MeasurableSpace Ω :=
  MeasurableSpace.comap (fun ω (p : ι × Set.Iic s) => B p.1 p.2 ω) inferInstance

theorem ginibreBrownianFamilyPastSpace_mono {Ω ι : Type*} (B : ι → ℝ≥0 → Ω → ℝ) :
    Monotone (ginibreBrownianFamilyPastSpace B) := by
  intro s t hst
  let R : (ι × Set.Iic t → ℝ) → (ι × Set.Iic s → ℝ) :=
    fun p q => p (q.1, ⟨q.2, q.2.property.trans hst⟩)
  have hR : Measurable R := by fun_prop
  change MeasurableSpace.comap (R ∘ fun ω (p : ι × Set.Iic t) => B p.1 p.2 ω) inferInstance ≤ _
  rw [← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono hR.comap_le

theorem ginibreBrownianFamilyPastSpace_le {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (s : ℝ≥0) :
    ginibreBrownianFamilyPastSpace B s ≤ (inferInstance : MeasurableSpace Ω) := by
  apply Measurable.comap_le
  apply measurable_pi_lambda
  intro p
  exact aemeasurable_iff_measurable.mp ((hB p.1).aemeasurable p.2)

def ginibreBrownianFamilyFiltration {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω) where
  seq := ginibreBrownianFamilyPastSpace B
  mono' := ginibreBrownianFamilyPastSpace_mono B
  le' := ginibreBrownianFamilyPastSpace_le B P hB

theorem ginibreBrownianFamilyFiltration_coordinate_stronglyAdapted {Ω ι : Type*} [MeasurableSpace Ω]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (i : ι) :
    StronglyAdapted (ginibreBrownianFamilyFiltration B P hB) (B i) := by
  intro s
  have hPast : @Measurable Ω (ι × Set.Iic s → ℝ) (ginibreBrownianFamilyPastSpace B s)
      inferInstance (fun ω p => B p.1 p.2 ω) := Measurable.of_comap_le le_rfl
  exact ((measurable_pi_apply (i, ⟨s, by change s ≤ s; exact le_rfl⟩)).comp hPast).stronglyMeasurable

end
end GinibrePoincare
