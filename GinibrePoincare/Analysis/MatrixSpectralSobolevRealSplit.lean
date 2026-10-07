module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevCoordinates
public import GinibrePoincare.Analysis.MatrixSpectralSobolevLocalSlices
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.Calculus.Deriv.Prod

@[expose] public section

/-! # Actual real-line coordinate splitting, including ordinary volume -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def configurationRealFirstSplit (d : ℕ) :
    (ℝ × (ℝ × Configuration d)) ≃L[ℝ] Configuration (d + 1) where
  toFun q := Fin.cons (Complex.equivRealProdCLM.symm (q.1, q.2.1)) q.2.2
  invFun z := ((z 0).re, (z 0).im, Fin.tail z)
  left_inv q := by cases q; rfl
  right_inv z := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_add' q r := by funext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  map_smul' r q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using (Complex.equivRealProdCLM.symm.map_smul r (q.1, q.2.1))
    · rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem configurationRealFirstSplit_volume_preserving (d : ℕ) :
    MeasurePreserving (configurationRealFirstSplit d)
      (volume : Measure (ℝ × (ℝ × Configuration d))) volume := by
  have h₁ := (volume_preserving_prodAssoc (α₁ := ℝ) (β₁ := ℝ)
    (γ₁ := Configuration d)).symm MeasurableEquiv.prodAssoc
  have h₂ := ((Complex.volume_preserving_equiv_real_prod).symm
    Complex.measurableEquivRealProd).prod (MeasurePreserving.id (volume : Measure (Configuration d)))
  have h₃ := (volume_preserving_piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0).symm
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => ℂ) 0)
  convert h₃.comp (h₂.comp h₁) using 1
  all_goals try rfl
  funext q i
  refine Fin.cases ?_ (fun j => ?_) i <;>
    simp [configurationRealFirstSplit, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv,
      MeasurableEquiv.prodAssoc, Complex.measurableEquivRealProd]
  all_goals rfl

theorem configurationRealFirstSplit_locallyIntegrable (d : ℕ)
    (f : Configuration (d + 1) → ℝ) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (f ∘ configurationRealFirstSplit d) volume := by
  apply (locallyIntegrable_map_homeomorph (configurationRealFirstSplit d).toHomeomorph).mp
  change LocallyIntegrable f (Measure.map (configurationRealFirstSplit d) volume)
  rw [(configurationRealFirstSplit_volume_preserving d).map_eq]
  exact hf

theorem configurationRealFirstSplit_line_hasDerivAt (d : ℕ)
    (y : ℝ × Configuration d) (t : ℝ) :
    HasDerivAt (fun s : ℝ => configurationRealFirstSplit d (s, y))
      (Fin.cons (1 : ℂ) 0) t := by
  apply hasDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change HasDerivAt (fun s : ℝ => Complex.equivRealProdCLM.symm (s, y.1)) 1 t
    convert Complex.equivRealProdCLM.symm.hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_id t).prodMk (hasDerivAt_const t y.1)) using 1 <;> rfl
  · simpa [configurationRealFirstSplit] using hasDerivAt_const t (y.2 j)

end
end GinibrePoincare
