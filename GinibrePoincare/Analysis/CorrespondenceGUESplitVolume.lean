module
public import GinibrePoincare.Analysis.CorrespondenceGUESplitDensity
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueSplitIndex (n : ℕ) : Fin n⊕Fin n ≃ Fin n×Fin 2 where
  toFun := Sum.elim (fun i => (i, 0)) (fun i => (i, 1))
  invFun p := if p.2=0 then Sum.inl p.1 else Sum.inr p.1
  left_inv s := by cases s <;> simp
  right_inv p := by
    rcases p with ⟨i, j⟩
    fin_cases j <;> simp

def gueSplitMeasurableEquiv (n : ℕ) : EuclideanSpace ℝ (Fin n×Fin 2) ≃ᵐ
    EuclideanSpace ℝ (Fin n)×EuclideanSpace ℝ (Fin n) :=
  (MeasurableEquiv.toLp 2 (Fin n×Fin 2→ℝ)).symm |>.trans
    ((MeasurableEquiv.piCongrLeft (fun _ : Fin n⊕Fin n => ℝ) (gueSplitIndex n).symm).trans
      ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n⊕Fin n => ℝ)).trans
        ((MeasurableEquiv.toLp 2 (Fin n→ℝ)).prodCongr (MeasurableEquiv.toLp 2 (Fin n→ℝ)))))

theorem gueSplitMeasurableEquiv_apply (n : ℕ) (x : EuclideanSpace ℝ (Fin n×Fin 2)) :
    gueSplitMeasurableEquiv n x=(gueRealProjection n x, gueAuxProjection n x) := by
  rfl

theorem gueSplit_volume_preserving (n : ℕ) :
    MeasurePreserving (gueSplitMeasurableEquiv n) volume (volume.prod volume) := by
  have h₁ := (PiLp.volume_preserving_toLp (Fin n×Fin 2)).symm
    (MeasurableEquiv.toLp 2 (Fin n×Fin 2→ℝ))
  have h₂ := volume_measurePreserving_piCongrLeft
    (fun _ : Fin n⊕Fin n => ℝ) (gueSplitIndex n).symm
  have h₃ := volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin n⊕Fin n => ℝ)
  have h₄ := (PiLp.volume_preserving_toLp (Fin n)).prod (PiLp.volume_preserving_toLp (Fin n))
  exact h₄.comp (h₃.comp (h₂.comp h₁))

#print axioms gueSplit_volume_preserving
end
end GinibrePoincare
