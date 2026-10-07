module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates
public import GinibrePoincare.Analysis.MatrixSpectralSobolevDensity

@[expose] public section

/-! # Actual Gaussian density and probability transport through entry coordinates -/
open MeasureTheory Matrix Filter
open scoped ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem measurePreserving_actual_withDensity
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) (f : X → Y) (hf : MeasurePreserving f μ ν)
    (ρ : Y → ℝ≥0∞) (hρ : Measurable ρ) :
    MeasurePreserving f (μ.withDensity (ρ ∘ f)) (ν.withDensity ρ) := by
  refine ⟨hf.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hf.measurable hs,
    withDensity_apply _ (hf.measurable hs), withDensity_apply _ hs,
    ← lintegral_indicator (hf.measurable hs), ← lintegral_indicator hs]
  convert hf.lintegral_comp (hρ.indicator hs) using 1
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ s <;> simp [hx, Function.comp_def]

def matrixEntryGaussianMeasure {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    Measure (Configuration m) :=
  (volume : Measure (Configuration m)).withDensity
    (fun z => matrixGaussianDensity n (Matrix.of (matrixComplexEntryEquiv e z)))

theorem matrixComplexEntryEquiv_gaussian_preserving {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) :
    MeasurePreserving (matrixComplexEntryEquiv e) (matrixEntryGaussianMeasure e)
      (matrixGaussianMeasure n) := by
  rw [matrixGaussianMeasure_eq_withDensity hn]
  exact measurePreserving_actual_withDensity volume volume (matrixComplexEntryEquiv e)
    (matrixComplexEntryEquiv_volume_preserving e) (matrixGaussianDensity n)
    (measurable_matrixGaussianDensity n)


theorem matrixEntryGaussianMeasure_isProbability {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) : IsProbabilityMeasure (matrixEntryGaussianMeasure e) := by
  constructor
  have he := (matrixComplexEntryEquiv_gaussian_preserving hn e).measure_preimage
    ((MeasurableSet.univ : MeasurableSet (Set.univ : Set (MatrixRealSpace n))).nullMeasurableSet)
  rw [Set.preimage_univ] at he
  exact he.trans (measure_univ (μ := matrixGaussianMeasure n))

def matrixEntryGaussianDensityReal {n m : ℕ} (e : Fin m ≃ Fin n × Fin n)
    (z : Configuration m) : ℝ :=
  matrixGaussianDensityReal n (Matrix.of (matrixComplexEntryEquiv e z))

theorem matrixEntryGaussianDensityReal_continuous {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) : Continuous (matrixEntryGaussianDensityReal e) := by
  unfold matrixEntryGaussianDensityReal matrixGaussianDensityReal
  simp only [matrixHSNormSq_eq_sum]
  fun_prop

theorem matrixEntryGaussianDensityReal_pos {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (z : Configuration m) :
    0 < matrixEntryGaussianDensityReal e z :=
  matrixGaussianDensityReal_pos n hn _

theorem matrixEntryGaussianMeasure_eq_real_density {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) : matrixEntryGaussianMeasure e =
    (volume : Measure (Configuration m)).withDensity
      (fun z => ENNReal.ofReal (matrixEntryGaussianDensityReal e z)) := rfl

theorem matrixEntryGaussianMeasure_le_finite_smul_volume {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) :
    ∃ c : ℝ≥0∞, c ≠ ∞ ∧ matrixEntryGaussianMeasure e ≤
      c • (volume : Measure (Configuration m)) := by
  refine ⟨ENNReal.ofReal (((n : ℝ) / Real.pi) ^ (n * n)), ENNReal.ofReal_ne_top, ?_⟩
  rw [matrixEntryGaussianMeasure, ← withDensity_const]
  exact withDensity_mono (Eventually.of_forall fun z => matrixGaussianDensity_le_const n _)

end
end GinibrePoincare
