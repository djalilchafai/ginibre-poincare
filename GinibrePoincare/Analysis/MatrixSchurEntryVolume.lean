module

public import GinibrePoincare.Analysis.MatrixSchurLocalIntegration

@[expose] public section

open Matrix MeasureTheory OrderDual
open scoped Matrix Matrix.Norms.Operator
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000
set_option maxHeartbeats 400000

def schurLowerRawEquiv (n : ℕ) :
    {p : Fin n × Fin n // p.2 < p.1} ≃ SchurLowerIndex n where
  toFun p := ⟨toLex (p.val.2, toDual p.val.1), p.property⟩
  invFun q := ⟨(schurLowerRow q, schurLowerCol q), q.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

def schurUpperRawEquiv (n : ℕ) :
    {p : Fin n × Fin n // ¬p.2 < p.1} ≃ SchurUpperIndex n where
  toFun p := ⟨p.val, le_of_not_gt p.property⟩
  invFun q := ⟨q.val, not_lt_of_ge q.property⟩
  left_inv p := by apply Subtype.ext; rfl
  right_inv q := by apply Subtype.ext; rfl

theorem matrixVolume_uncurry_preserving (n : ℕ) :
    MeasurePreserving (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)) := by
  refine ⟨by fun_prop, ?_⟩
  change Measure.map Function.uncurry (Measure.pi (fun _ : Fin n =>
    Measure.pi (fun _ : Fin n => (volume : Measure ℂ)))) =
    Measure.pi (fun _ : Fin n × Fin n => (volume : Measure ℂ))
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : (Fin n → Fin n → ℂ) → (Fin n × Fin n → ℂ)) ⁻¹'
      Set.univ.pi s = Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext G
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.uncurry_apply_pair, Prod.forall]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_prod_type]

/-- Splitting matrix entries into lower and upper coordinates preserves actual product
Lebesgue volume; no Jacobian normalization constant is left implicit. -/
theorem schurEntryCoordinates_volume_preserving (n : ℕ) :
    MeasurePreserving (schurEntryCoordinates (n := n))
      (volume : Measure (Fin n → Fin n → ℂ)) (volume : Measure (SchurCoordinates n)) := by
  let P := fun p : Fin n × Fin n => p.2 < p.1
  let L := MeasurableEquiv.piCongrLeft (fun _ : SchurLowerIndex n => ℂ)
    (schurLowerRawEquiv n)
  let R := MeasurableEquiv.piCongrLeft (fun _ : SchurUpperIndex n => ℂ)
    (schurUpperRawEquiv n)
  have hL := measurePreserving_piCongrLeft
    (fun _ : SchurLowerIndex n => (volume : Measure ℂ))
    (schurLowerRawEquiv n)
  have hR := measurePreserving_piCongrLeft
    (fun _ : SchurUpperIndex n => (volume : Measure ℂ))
    (schurUpperRawEquiv n)
  have hsplit := measurePreserving_piEquivPiSubtypeProd
    (fun _ : Fin n × Fin n => (volume : Measure ℂ)) P
  have hp := (hL.prod hR).comp (hsplit.comp (matrixVolume_uncurry_preserving n))
  have hf : (fun G : Fin n → Fin n → ℂ =>
      (L ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n × Fin n => ℂ) P)
        (Function.uncurry G)).1,
       R ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n × Fin n => ℂ) P)
        (Function.uncurry G)).2)) = schurEntryCoordinates := by
    rfl
  rw [← hf]
  exact hp

#print axioms schurEntryCoordinates_volume_preserving
end
end GinibrePoincare
