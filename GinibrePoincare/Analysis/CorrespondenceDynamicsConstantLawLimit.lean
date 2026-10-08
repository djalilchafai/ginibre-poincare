module
public import GinibrePoincare.Analysis.CorrespondenceDynamicsNoiseShift
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Constant finite laws pass to almost surely convergent measurable random elements. -/
theorem correspondence_constantLaw_ae_limit {Ω E : Type*} [MeasurableSpace Ω]
    [TopologicalSpace E] [HasOuterApproxClosed E] [MeasurableSpace E] [BorelSpace E]
    (P : Measure Ω) [IsFiniteMeasure P] (X : ℕ → Ω → E) (x : Ω → E)
    (hX : ∀ m, Measurable (X m)) (hx : Measurable x)
    (hl : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (x ω)))
    (ν : Measure E) [IsFiniteMeasure ν] (he : ∀ m, P.map (X m) = ν) :
    P.map x = ν := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro b
  rw [integral_map hx.aemeasurable b.continuous.aestronglyMeasurable]
  have ht : Tendsto (fun m => ∫ ω, b (X m ω) ∂P) atTop (𝓝 (∫ ω, b (x ω) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖b‖)
    · intro m
      exact (b.continuous.measurable.comp (hX m)).aestronglyMeasurable
    · exact integrable_const _
    · intro m
      exact Eventually.of_forall (fun ω => b.norm_coe_le_norm _)
    · filter_upwards [hl] with ω hω
      exact b.continuous.continuousAt.tendsto.comp hω
  have he' (m : ℕ) : (∫ ω, b (X m ω) ∂P) = ∫ y, b y ∂ν := by
    rw [← he m,integral_map (hX m).aemeasurable b.continuous.aestronglyMeasurable]
  exact (tendsto_nhds_unique ht (by simpa only [he'] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => ∫ y, b y ∂ν) atTop (𝓝 (∫ y, b y ∂ν)))))

#print axioms correspondence_constantLaw_ae_limit
end
end GinibrePoincare
