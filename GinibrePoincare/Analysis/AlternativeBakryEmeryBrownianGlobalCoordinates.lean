module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalGaussian
public import GinibrePoincare.Analysis.GinibreHamiltonianCompletedProductBrownian
@[expose] public section
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (ι : Type*) [Fintype ι]

abbrev BakryBrownianCoordinateSample :=
  NullMeasurableSpace (ι → BakryBrownianGlobalSample)
    (Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure))

def bakryBrownianCoordinateMeasure : Measure (BakryBrownianCoordinateSample ι) :=
  (Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure)).completion

instance : IsProbabilityMeasure (bakryBrownianCoordinateMeasure ι) :=
  ginibre_completion_isProbabilityMeasure _
instance : (bakryBrownianCoordinateMeasure ι).IsComplete :=
  Measure.completion.isComplete _

def bakryBrownianCoordinateProcess (i : ι) (t : ℝ≥0)
    (ω : BakryBrownianCoordinateSample ι) : ℝ := bakryBrownianGlobalProcess t (ω i)

lemma bakryBrownianCoordinate_eval_preserving (i : ι) :
    MeasurePreserving (fun ω : BakryBrownianCoordinateSample ι => ω i)
      (bakryBrownianCoordinateMeasure ι) bakryBrownianGlobalMeasure := by
  refine ⟨(measurable_pi_apply i).nullMeasurable.measurable',?_⟩
  change (Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure)).completion.map
    (fun ω => ω i) = _
  rw [ginibre_map_completion _ _ (measurable_pi_apply i)]
  exact (measurePreserving_eval (fun _ : ι => bakryBrownianGlobalMeasure) i).map_eq

lemma bakryBrownianCoordinate_isBrownian_of_scalar
    (hB : IsBrownianReal bakryBrownianGlobalProcess bakryBrownianGlobalMeasure) :
    ∀ i, IsBrownianReal (bakryBrownianCoordinateProcess ι i) (bakryBrownianCoordinateMeasure ι) := by
  intro i
  exact ginibreBrownian_precompose_measurePreserving _ _ _
    (bakryBrownianCoordinate_eval_preserving ι i) _ hB

lemma bakryBrownianCoordinate_independent :
    iIndepFun (fun i ω t => bakryBrownianCoordinateProcess ι i t ω)
      (bakryBrownianCoordinateMeasure ι) := by
  let μ := Measure.pi (fun _ : ι => bakryBrownianGlobalMeasure)
  have hp : MeasurePreserving (fun ω : BakryBrownianCoordinateSample ι =>
      (fun i => ω i)) (bakryBrownianCoordinateMeasure ι) μ := by
    have hId : @Measurable (ι → BakryBrownianGlobalSample) (ι → BakryBrownianGlobalSample)
        MeasurableSpace.pi MeasurableSpace.pi id := measurable_id
    refine ⟨hId.nullMeasurable.measurable',?_⟩
    have he := ginibre_map_completion μ id hId
    simpa only [id_eq, Measure.map_id, bakryBrownianCoordinateMeasure, μ] using he
  have hm : Measurable (fun ω : BakryBrownianGlobalSample => fun t => bakryBrownianGlobalProcess t ω) :=
    Measurable.of_eval (fun t => bakryBrownianGlobalPath_eval_measurable t)
  exact ginibre_iIndepFun_precompose_measurePreserving _ μ _ hp
    (fun i ω t => bakryBrownianGlobalProcess t (ω i))
    (fun i => hm.comp (measurable_pi_apply i))
    (iIndepFun_pi (X := fun _ ω t => bakryBrownianGlobalProcess t ω) (fun _ => hm.aemeasurable))

#print axioms bakryBrownianCoordinate_eval_preserving
#print axioms bakryBrownianCoordinate_isBrownian_of_scalar
#print axioms bakryBrownianCoordinate_independent
end
end GinibrePoincare
