module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryVectorSpectralMeasure
public import GinibrePoincare.Analysis.AlternativeSpectralSupport

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual scalar spectral measure of every vector for the concrete
Ginibre symmetric complex resolvent, on the real spectral line. -/
def ginibreResolventVectorSpectralMeasure (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : Measure ℝ :=
  (vectorSpectralMeasure (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isSelfAdjoint n hn) u).map Subtype.val

theorem ginibreResolventVectorSpectralMeasure_mass (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreResolventVectorSpectralMeasure n hn u univ = ENNReal.ofReal (‖u‖^2) := by
  unfold ginibreResolventVectorSpectralMeasure
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ]
  simp only [preimage_univ]
  exact vectorSpectralMeasure_mass _ _ _

/-- Literal vector-measure support, rather than only operator graph-spectrum
support: no vector has scalar resolvent spectral mass outside [0,1/3]∪{1}. -/
theorem ginibreResolventVectorSpectralMeasure_support (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreResolventVectorSpectralMeasure n hn u (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ = 0 := by
  unfold ginibreResolventVectorSpectralMeasure
  rw [Measure.map_apply measurable_subtype_coe (measurableSet_Icc.union (measurableSet_singleton 1)).compl]
  have he : (Subtype.val : spectrum ℝ (ginibreFullComplexResolvent n hn) → ℝ) ⁻¹'
      (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ = ∅ := by
    ext r
    simp only [mem_preimage, mem_compl_iff, mem_empty_iff_false, iff_false, not_not]
    exact spectral_ginibre_resolvent_spectrum_support n hn r.property
  rw [he, measure_empty]

#print axioms ginibreResolventVectorSpectralMeasure
#print axioms ginibreResolventVectorSpectralMeasure_mass
#print axioms ginibreResolventVectorSpectralMeasure_support
end
end GinibrePoincare
