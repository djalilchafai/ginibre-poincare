module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryVectorZeroAtom

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The inverse-resolvent transformation from the positive resolvent spectral
coordinate to the concrete speed-n generator spectral coordinate. -/
def inverseResolventSpectralCoordinate (r : ℝ) : ℝ := 1-r⁻¹

theorem measurable_inverseResolventSpectralCoordinate :
    Measurable inverseResolventSpectralCoordinate := measurable_const.sub measurable_inv

/-- Literal vector spectral measure of the concrete symmetric Ginibre
full generator, obtained from its internally constructed resolvent vector
measure. The totalized value at r=0 is immaterial by the proved zero-atom lemma. -/
def ginibreGeneratorVectorSpectralMeasure (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) : Measure ℝ :=
  (ginibreResolventVectorSpectralMeasure n hn u).map inverseResolventSpectralCoordinate

theorem ginibreGeneratorVectorSpectralMeasure_mass (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreGeneratorVectorSpectralMeasure n hn u univ = ENNReal.ofReal (‖u‖^2) := by
  unfold ginibreGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_inverseResolventSpectralCoordinate MeasurableSet.univ]
  simp only [preimage_univ]
  exact ginibreResolventVectorSpectralMeasure_mass n hn u

/-- Section 3's literal scalar vector spectral support: every vector measure
is concentrated on {0}∪(−∞,−2], with no supplied spectral measure hypothesis. -/
theorem ginibreGeneratorVectorSpectralMeasure_support (n : ℕ) (hn : 0 < n)
    (u : ginibreSymmetricL2 n) :
    ginibreGeneratorVectorSpectralMeasure n hn u ({0} ∪ Iic (-2 : ℝ))ᶜ = 0 := by
  unfold ginibreGeneratorVectorSpectralMeasure
  rw [Measure.map_apply measurable_inverseResolventSpectralCoordinate
    ((measurableSet_singleton 0).union measurableSet_Iic).compl]
  let μ := ginibreResolventVectorSpectralMeasure n hn u
  have hsub : inverseResolventSpectralCoordinate ⁻¹' ({0} ∪ Iic (-2 : ℝ))ᶜ ⊆
      {0} ∪ (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ := by
    intro r hr
    by_cases hz : r = 0
    · exact Or.inl hz
    · right
      intro hs
      apply hr
      rcases hs with hs | hs
      · right
        have hpos : 0 < r := lt_of_le_of_ne hs.1 (Ne.symm hz)
        have hi : 3 ≤ r⁻¹ := (by simpa using one_div_le_one_div_of_le hpos hs.2)
        change 1-r⁻¹ ≤ -2
        linarith
      · left
        change r=1 at hs
        simp [inverseResolventSpectralCoordinate,hs]
  apply le_antisymm _ bot_le
  calc
    _ ≤ μ ({0} ∪ (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ) := measure_mono hsub
    _ ≤ μ {0} + μ (Icc (0 : ℝ) (1/3) ∪ {1})ᶜ := measure_union_le _ _
    _ = 0 := by rw [ginibreResolventVectorSpectralMeasure_zero_atom,
      ginibreResolventVectorSpectralMeasure_support,add_zero]

#print axioms ginibreGeneratorVectorSpectralMeasure
#print axioms ginibreGeneratorVectorSpectralMeasure_mass
#print axioms ginibreGeneratorVectorSpectralMeasure_support
end
end GinibrePoincare
