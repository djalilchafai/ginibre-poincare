module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialTests
public import GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialImagTests

@[expose] public section

/-! # Moving an arbitrary entry derivative to the actual first coordinate -/
open MeasureTheory MvPolynomial
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def configurationFirstReindex {d : ℕ} (j : Fin (d + 1)) :
    Configuration (d + 1) ≃L[ℝ] Configuration (d + 1) :=
  { toFun := fun z i => z (Equiv.swap 0 j i)
    invFun := fun z i => z (Equiv.swap 0 j i)
    left_inv := by intro z; funext i; simp
    right_inv := by intro z; funext i; simp
    map_add' := by intros; rfl
    map_smul' := by intros; rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

theorem configurationFirstReindex_direction {d : ℕ} (j : Fin (d + 1)) (a : ℂ) :
    configurationFirstReindex j (Fin.cons a 0) = coordinateDirection j a := by
  classical
  have he : (Fin.cons a 0 : Configuration (d + 1)) = Pi.single 0 a := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> simp
  rw [he]
  funext i
  change (Pi.single 0 a : Configuration (d + 1)) (Equiv.swap 0 j i) = coordinateDirection j a i
  simp only [coordinateDirection, Pi.single_apply]
  have hi : Equiv.swap 0 j i = 0 ↔ i = j := by
    rw [← Equiv.eq_symm_apply]
    simp
  simp [hi]

theorem configurationFirstReindex_volume_preserving {d : ℕ} (j : Fin (d + 1)) :
    MeasurePreserving (configurationFirstReindex j) volume volume := by
  have h := volume_measurePreserving_piCongrLeft (fun _ : Fin (d + 1) => ℂ) (Equiv.swap 0 j)
  convert h using 1
  funext z i
  change z (Equiv.swap 0 j i) = (Equiv.piCongrLeft (fun _ : Fin (d + 1) => ℂ) (Equiv.swap 0 j)) z i
  rw [Equiv.piCongrLeft_apply]
  simp

theorem configurationFirstReindex_locallyIntegrable {d : ℕ} (j : Fin (d + 1))
    (f : Configuration (d + 1) → ℝ) (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (f ∘ configurationFirstReindex j) volume := by
  apply (locallyIntegrable_map_homeomorph (configurationFirstReindex j).toHomeomorph).mp
  change LocallyIntegrable f (Measure.map (configurationFirstReindex j) volume)
  rw [(configurationFirstReindex_volume_preserving j).map_eq]
  exact hf

end
end GinibrePoincare
