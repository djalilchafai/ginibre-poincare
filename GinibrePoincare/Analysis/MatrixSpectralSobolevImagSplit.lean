module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates
public import GinibrePoincare.Analysis.MatrixSpectralSobolevLocalSlices
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! # Actual imaginary-line coordinate splitting, including ordinary volume -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def configurationImagFirstSplit (d : ℕ) :
    (ℝ × (ℝ × Configuration d)) ≃L[ℝ] Configuration (d + 1) where
  toFun q := Fin.cons (Complex.equivRealProdCLM.symm (q.2.1, q.1)) q.2.2
  invFun z := ((z 0).im, (z 0).re, Fin.tail z)
  left_inv q := by cases q; rfl
  right_inv z := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' q r := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' r q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (Complex.equivRealProdCLM.symm.map_smul r (q.2.1, q.1))
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem configurationImagFirstSplit_volume_preserving (d : ℕ) :
    MeasurePreserving (configurationImagFirstSplit d)
      (volume : Measure (ℝ × (ℝ × Configuration d))) volume := by
  have h₁ := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ)
    (γ₁ := Configuration d)).symm MeasurableEquiv.prodAssoc
  have hswap := (Measure.measurePreserving_swap
    (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).prod
    (MeasurePreserving.id (volume : Measure (Configuration d)))
  have h₂ := ((Complex.volume_preserving_equiv_real_prod).symm
    Complex.measurableEquivRealProd).prod (MeasurePreserving.id (volume : Measure (Configuration d)))
  have h₃ := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0)
  convert h₃.comp (h₂.comp (hswap.comp h₁)) using 1
  all_goals try rfl
  funext q i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [configurationImagFirstSplit, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.prodAssoc, Complex.measurableEquivRealProd]
  all_goals rfl

theorem configurationImagFirstSplit_locallyIntegrable (d : ℕ)
    (f : Configuration (d + 1) → ℝ) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (f ∘ configurationImagFirstSplit d) volume := by
  apply (locallyIntegrable_map_homeomorph (configurationImagFirstSplit d).toHomeomorph).mp
  change LocallyIntegrable f (Measure.map (configurationImagFirstSplit d) volume)
  rw [(configurationImagFirstSplit_volume_preserving d).map_eq]
  exact hf

theorem configurationImagFirstSplit_line_hasDerivAt (d : ℕ)
    (y : ℝ × Configuration d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => configurationImagFirstSplit d (s, y))
      (Fin.cons Complex.I 0) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change HasDerivAt (fun s : ℝ => Complex.equivRealProdCLM.symm (y.1, s)) Complex.I t
    convert Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t y.1).prodMk (hasDerivAt_id t)) using 1 <;> rfl
  · simpa [configurationImagFirstSplit] using hasDerivAt_const t (y.2 j)

end
end GinibrePoincare
