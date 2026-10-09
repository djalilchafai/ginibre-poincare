module
public import GinibrePoincare.Analysis.CorrespondenceGUEPaperH1
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueFullMeasure_permutation_integral (n : ℕ) (σ : Equiv.Perm (Fin n))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫x, f (guePermute n σ x) ∂gueFullMeasure n)=(∫x, f x ∂gueFullMeasure n) := by
  rw [gueFullMeasure_integral, gueFullMeasure_integral]
  congr 1
  have h := (guePermute_volume_preserving n σ).integral_comp
    (guePermuteIsometry n σ).toMeasurableEquiv.measurableEmbedding
    (fun x => gueRawDensity n x*f x)
  have he x : gueRawDensity n (guePermute n σ x)=gueRawDensity n x := gueRawDensity_symmetric n σ x
  simpa only [he] using h

theorem gueFullMeasure_permutation_preserving {n : ℕ} (hn : 0<n) (σ : Equiv.Perm (Fin n)) :
    MeasurePreserving (guePermute n σ) (gueFullMeasure n) (gueFullMeasure n) := by
  letI := gueFullMeasure_probability hn
  have hm : Measurable (guePermute n σ) := (guePermuteIsometry n σ).continuous.measurable
  refine ⟨hm, Measure.ext (fun s hs => ?_)⟩
  have hi := gueFullMeasure_permutation_integral n σ (s.indicator (fun _ => 1))
  rw [← integral_map hm.aemeasurable (by exact (measurable_const.indicator hs).aestronglyMeasurable)] at hi
  change (∫x, s.indicator (1 : EuclideanSpace ℝ (Fin n)→ℝ) x ∂(gueFullMeasure n).map (guePermute n σ))=
    (∫x, s.indicator (1 : EuclideanSpace ℝ (Fin n)→ℝ) x ∂gueFullMeasure n) at hi
  rw [integral_indicator_one hs, integral_indicator_one hs] at hi
  calc
    (gueFullMeasure n).map (guePermute n σ) s=
        ENNReal.ofReal (((gueFullMeasure n).map (guePermute n σ) s).toReal) :=
      (ENNReal.ofReal_toReal (measure_lt_top _ _).ne).symm
    _ = ENNReal.ofReal ((gueFullMeasure n s).toReal) := congrArg ENNReal.ofReal hi
    _ = gueFullMeasure n s := ENNReal.ofReal_toReal (measure_lt_top _ _).ne

#print axioms gueFullMeasure_permutation_preserving
end
end GinibrePoincare
