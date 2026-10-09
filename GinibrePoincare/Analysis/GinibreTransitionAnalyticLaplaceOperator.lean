module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceBounds

@[expose] public section

open MeasureTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Literal normalized Laplace integration is a genuine linear map. -/
def actualContractionLaplaceLinear {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖≤‖u‖) (c : ℝ) (hc : 0<c) : E →ₗ[ℝ] E where
  toFun u := ∫ s in Ioi (0 : ℝ), (c*Real.exp (-c*s)) • A s.toNNReal u
  map_add' u v := by
    simp only [map_add, smul_add]
    exact integral_add (actualContractionLaplace_integrable A hcont hbound c hc u)
      (actualContractionLaplace_integrable A hcont hbound c hc v)
  map_smul' d u := by
    simp only [map_smul, RingHom.id_apply]
    have he : (fun s : ℝ => (c*Real.exp (-c*s)) • d • A s.toNNReal u)=
        (fun s => d • (c*Real.exp (-c*s)) • A s.toNNReal u) := by
      funext s
      exact smul_comm _ _ _
    rw [he, integral_smul]

/-- The literal normalized Laplace operator is a contraction, internally
bounded using the true mass-one exponential weight. -/
theorem actualContractionLaplaceLinear_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖≤‖u‖) (c : ℝ) (hc : 0<c) (u : E) :
    ‖actualContractionLaplaceLinear A hcont hbound c hc u‖≤‖u‖ := by
  exact (actualNormalizedLaplaceIntegral_norm_bound
    (fun s : ℝ => A s.toNNReal u) c ‖u‖ hc
    (((hcont u).comp continuous_real_toNNReal).aestronglyMeasurable)
    (ae_of_all _ fun s => hbound _ _)).2

/-- The actual normalized Bochner Laplace transform, as a continuous linear
operator on the original Hilbert space. -/
def actualContractionLaplaceOperator {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A : ℝ≥0 → E →L[ℝ] E) (hcont : ∀ u, Continuous (fun t => A t u))
    (hbound : ∀ t u, ‖A t u‖≤‖u‖) (c : ℝ) (hc : 0<c) : E →L[ℝ] E :=
  (actualContractionLaplaceLinear A hcont hbound c hc).mkContinuous 1
    (fun u => by simpa only [one_mul] using
      actualContractionLaplaceLinear_norm_bound A hcont hbound c hc u)

#print axioms actualContractionLaplaceLinear
#print axioms actualContractionLaplaceLinear_norm_bound
#print axioms actualContractionLaplaceOperator
end
end GinibrePoincare
