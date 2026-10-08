module

public import GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Split off one genuine complex particle coordinate from product Lebesgue measure. -/
def correspondenceCollisionSplit {n : ℕ} (j : Fin n) :
    Configuration n ≃ᵐ ℂ × ({k : Fin n // k ≠ j} → ℂ) := by
  classical
  letI : Unique {k : Fin n // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k => Subtype.ext k.property⟩
  exact (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℂ) (fun k => k = j)).trans
    ((MeasurableEquiv.piUnique (fun _ : {k : Fin n // k = j} => ℂ)).prodCongr
      (MeasurableEquiv.refl _))

theorem correspondenceCollisionSplit_apply {n : ℕ} (j : Fin n) (z : Configuration n) :
    correspondenceCollisionSplit j z = (z j, fun k => z k.val) := by
  rfl

theorem correspondenceCollisionSplit_volume {n : ℕ} (j : Fin n) :
    MeasurePreserving (correspondenceCollisionSplit j)
      (volume : Measure (Configuration n)) volume := by
  classical
  letI : Unique {k : Fin n // k = j} :=
    ⟨⟨⟨j, rfl⟩⟩, fun k => Subtype.ext k.property⟩
  have hs := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n => (volume : Measure ℂ)) (fun k => k = j)
  rw [show Subtype.fintype (fun k : Fin n => k = j) = Fintype.subtypeEq j
    from Subsingleton.elim _ _] at hs
  have h := ((measurePreserving_piUnique (fun _ : {k : Fin n // k = j} =>
      (volume : Measure ℂ))).prod
    (MeasurePreserving.id (Measure.pi fun _ : {k : Fin n // k ≠ j} =>
      (volume : Measure ℂ)))).comp
    hs
  simp only [Measure.volume_eq_prod, volume_pi] at h ⊢
  convert h using 1
  funext z
  rfl

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceCollisionSplit_volume
