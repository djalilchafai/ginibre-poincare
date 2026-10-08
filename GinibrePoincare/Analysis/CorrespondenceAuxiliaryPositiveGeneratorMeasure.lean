module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryVectorSemigroupRepresentation

@[expose] public section
open MeasureTheory Set
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- The paper's nonnegative `-Lₙ` spectral coordinate. -/
def ginibreNegativeGeneratorVectorSpectralMeasure (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : Measure ℝ :=
  (ginibreGeneratorVectorSpectralMeasure n hn u).map (fun x : ℝ => -x)

theorem ginibreNegativeGeneratorVectorSpectralMeasure_mass (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreNegativeGeneratorVectorSpectralMeasure n hn u univ = ENNReal.ofReal (‖u‖^2) := by
  unfold ginibreNegativeGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_neg MeasurableSet.univ]
  simpa using ginibreGeneratorVectorSpectralMeasure_mass n hn u

theorem ginibreNegativeGeneratorVectorSpectralMeasure_support (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreNegativeGeneratorVectorSpectralMeasure n hn u ({0} ∪ Ici (2 : ℝ))ᶜ = 0 := by
  unfold ginibreNegativeGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_neg
    ((measurableSet_singleton 0).union measurableSet_Ici).compl]
  have he : (fun x : ℝ => -x) ⁻¹' ({0} ∪ Ici (2 : ℝ))ᶜ =
      ({0} ∪ Iic (-2 : ℝ))ᶜ := by
    ext x
    have hneg : (2 : ℝ) ≤ -x ↔ x ≤ -2 := by constructor <;> intro h <;> linarith
    simp only [mem_preimage,mem_compl_iff,mem_union,mem_singleton_iff,mem_Ici,mem_Iic,
      neg_eq_zero,hneg]
  rw [he]
  exact ginibreGeneratorVectorSpectralMeasure_support n hn u

theorem ginibreNegativeGeneratorVectorSpectralMeasure_semigroup (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) (t : ℝ≥0) :
    (∫ lam : ℝ, Real.exp (-(t : ℝ)*lam)
      ∂ginibreNegativeGeneratorVectorSpectralMeasure n hn u) =
      (inner ℂ u (ginibreFullEvolution n hn t u)).re := by
  unfold ginibreNegativeGeneratorVectorSpectralMeasure
  rw [integral_map measurable_neg.aemeasurable
    (show AEStronglyMeasurable (fun lam : ℝ => Real.exp (-(t : ℝ)*lam))
      (Measure.map (fun x : ℝ => -x) (ginibreGeneratorVectorSpectralMeasure n hn u)) from
      (by fun_prop : Continuous (fun lam : ℝ => Real.exp (-(t : ℝ)*lam))).aestronglyMeasurable)]
  simp only [neg_mul_neg]
  exact ginibreGeneratorVectorSpectralMeasure_semigroup n hn u t

#print axioms ginibreNegativeGeneratorVectorSpectralMeasure_mass
#print axioms ginibreNegativeGeneratorVectorSpectralMeasure_support
#print axioms ginibreNegativeGeneratorVectorSpectralMeasure_semigroup
end
end GinibrePoincare
