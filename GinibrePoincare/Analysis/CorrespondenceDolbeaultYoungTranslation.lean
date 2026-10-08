module
public import GinibrePoincare.Analysis.GaussianClosedFormVolume
public import Mathlib.Topology.CompactOpen
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev dolbeaultOrdinaryL2 (n : ℕ) := Lp ℂ 2 (volume : Measure (Configuration n))

def dolbeaultCoordinateTranslation {n : ℕ} (j : Fin n) (y : ℂ) :
    C(Configuration n, Configuration n) :=
  ⟨fun z => z-Pi.single j y,continuous_id.sub continuous_const⟩

theorem dolbeaultCoordinateTranslation_preserving {n : ℕ} (j : Fin n) (y : ℂ) :
    MeasurePreserving (dolbeaultCoordinateTranslation j y)
      (volume : Measure (Configuration n)) volume := by
  exact measurePreserving_sub_right (volume : Measure (Configuration n)) (Pi.single j y : Configuration n)

def dolbeaultTranslateL2 {n : ℕ} (j : Fin n) (y : ℂ) :
    dolbeaultOrdinaryL2 n →ₗᵢ[ℂ] dolbeaultOrdinaryL2 n :=
  Lp.compMeasurePreservingₗᵢ ℂ (dolbeaultCoordinateTranslation j y)
    (dolbeaultCoordinateTranslation_preserving j y)

theorem dolbeaultTranslateL2_norm {n : ℕ} (j : Fin n) (y : ℂ)
    (u : dolbeaultOrdinaryL2 n) : ‖dolbeaultTranslateL2 j y u‖=‖u‖ :=
  (dolbeaultTranslateL2 j y).norm_map u

theorem dolbeaultCoordinateTranslation_continuous {n : ℕ} (j : Fin n) :
    Continuous (dolbeaultCoordinateTranslation j) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℂ × Configuration n => p.2-Pi.single j p.1)
  apply continuous_snd.sub
  apply continuous_pi
  intro k
  by_cases h : k=j
  · subst k
    simpa using continuous_fst
  · simpa [Pi.single_eq_of_ne h] using (continuous_const : Continuous (fun _ : ℂ × Configuration n => (0 : ℂ)))

theorem dolbeaultTranslateL2_continuous {n : ℕ} (j : Fin n) (u : dolbeaultOrdinaryL2 n) :
    Continuous (fun y => dolbeaultTranslateL2 j y u) := by
  exact continuous_const.compMeasurePreservingLp (dolbeaultCoordinateTranslation_continuous j)
    (dolbeaultCoordinateTranslation_preserving j) (by norm_num)

#print axioms dolbeaultTranslateL2_continuous
end
end GinibrePoincare
