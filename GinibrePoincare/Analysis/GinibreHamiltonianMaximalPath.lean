module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalSegments

@[expose] public section

/-! Canonical gluing of all actual local solutions before the maximal lifespan. -/
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenMaximalLifetime_exists_segment {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} (t : ℝ≥0) (ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    ∃ T : ℝ≥0, ∃ X : ℝ → Configuration n, t < T ∧ GinibreDrivenSegment n α N z T X := by
  obtain ⟨T, hT, htT⟩ := ginibreDrivenMaximalLifetime_exists_horizon t ht
  obtain ⟨X, hX⟩ := hT
  exact ⟨T, X, htT, hX⟩

def ginibreDrivenMaximalValue (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) (t : ℝ≥0) : Configuration n :=
  if ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z then
    let h := ginibreDrivenMaximalLifetime_exists_segment t ht
    (Classical.choose (Classical.choose_spec h)) (t : ℝ)
  else z

def ginibreDrivenMaximalPath (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) (t : ℝ) : Configuration n :=
  ginibreDrivenMaximalValue n α N z (Real.toNNReal t)

 theorem ginibreDrivenMaximalValue_eq_segment {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {T : ℝ≥0} {X : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X) (t : ℝ≥0) (htT : t ≤ T)
    (ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    ginibreDrivenMaximalValue n α N z t = X (t : ℝ) := by
  unfold ginibreDrivenMaximalValue
  rw [dif_pos ht]
  let h := ginibreDrivenMaximalLifetime_exists_segment t ht
  have hs := Classical.choose_spec (Classical.choose_spec h)
  exact hs.2.eqOn hX ⟨t.property, by exact_mod_cast (le_min hs.1.le htT)⟩

 theorem ginibreDrivenMaximalPath_eq_segment {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {T : ℝ≥0} {X : ℝ → Configuration n}
    (hX : GinibreDrivenSegment n α N z T X)
    (hT : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    EqOn (ginibreDrivenMaximalPath n α N z) X (Icc 0 (T : ℝ)) := by
  intro t ht
  have hNN : Real.toNNReal t ≤ T := (Real.toNNReal_le_iff_le_coe).mpr ht.2
  have hlt : (Real.toNNReal t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z :=
    (ENNReal.coe_le_coe.mpr hNN).trans_lt hT
  simpa only [ginibreDrivenMaximalPath, Real.coe_toNNReal t ht.1] using
    ginibreDrivenMaximalValue_eq_segment hX (Real.toNNReal t) hNN hlt

 theorem ginibreDrivenMaximalPath_segment {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} (T : ℝ≥0)
    (hT : (T : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    GinibreDrivenSegment n α N z T (ginibreDrivenMaximalPath n α N z) := by
  obtain ⟨U, X, hTU, hX⟩ := ginibreDrivenMaximalLifetime_exists_segment T hT
  have hXU : Icc (0 : ℝ) (T : ℝ) ⊆ Icc 0 (U : ℝ) :=
    Icc_subset_Icc_right (by exact_mod_cast hTU.le)
  have hXR : GinibreDrivenSegment n α N z T X :=
    ⟨hX.1.mono hXU, hX.2.1, fun t ht => hX.2.2 t (hXU ht)⟩
  have he := ginibreDrivenMaximalPath_eq_segment hXR hT
  have hcont := hXR.1.congr (fun t ht => he ht)
  have hzero := he ⟨le_rfl, T.property⟩
  refine ⟨hcont, hzero.trans hXR.2.1, ?_⟩
  intro t ht
  have hx := hXR.2.2 t ht
  rw [he ht]
  refine ⟨hx.1, ?_, ?_⟩
  · apply hx.2.1.congr
    intro u hu
    rw [uIoc_of_le ht.1] at hu
    exact congrArg (ginibreLangevinDrift n α) (he ⟨hu.1.le, hu.2.trans ht.2⟩).symm
  · rw [hx.2.2]
    congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht.1] at hu
    exact congrArg (ginibreLangevinDrift n α) (he ⟨hu.1, hu.2.trans ht.2⟩).symm

end
end GinibrePoincare
