module

public import GinibrePoincare.Analysis.NonQuadraticL2TensorOperators
public import Mathlib.MeasureTheory.Constructions.Pi

@[expose] public section

/-! # Actual finite-product coordinate operators -/
open MeasureTheory
open scoped InnerProductSpace
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- A measure preserving measurable equivalence induces a genuine unitary
between the actual L² spaces, in the pullback direction. -/
def l2PullbackEquiv {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he) (by
    intro F
    refine ⟨Lp.compMeasurePreserving e.symm (he.symm e) F, ?_⟩
    change Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) F) = F
    rw [← Lp.compMeasurePreserving_comp_apply]
    have hi : (e.symm : Y → X) ∘ e = id := by funext x; exact e.symm_apply_apply x
    simp only [hi, Lp.compMeasurePreserving_id_apply])

/-- Split off any chosen coordinate of a genuine finite product measure. -/
def l2PiCoordinateEquiv {m : ℕ} {X : Fin (m + 1) → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (i : Fin (m + 1)) :
    Lp ℂ 2 (Measure.pi μ) ≃ₗᵢ[ℂ]
      Lp ℂ 2 ((μ i).prod (Measure.pi (fun j => μ (i.succAbove j)))) :=
  (l2PullbackEquiv (MeasurableEquiv.piFinSuccAbove X i)
    (measurePreserving_piFinSuccAbove μ i)).symm

/-- Apply a bounded scalar operator in any chosen coordinate of an actual
finite product L² space. -/
def l2PiCoordinateOperator {m : ℕ} {X : Fin (m + 1) → Type*}
    [∀ i, MeasurableSpace (X i)] (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)]
    (i : Fin (m + 1)) (A : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i)) :
    Lp ℂ 2 (Measure.pi μ) →L[ℂ] Lp ℂ 2 (Measure.pi μ) :=
  (l2PiCoordinateEquiv μ i).symm.toLinearIsometry.toContinuousLinearMap.comp
    ((l2ProductLeftOperator A).comp (l2PiCoordinateEquiv μ i).toLinearIsometry.toContinuousLinearMap)
variable {m : ℕ} {X : Fin (m + 1) → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : ∀ i, Measure (X i)) [∀ i, SigmaFinite (μ i)] (i : Fin (m + 1))

theorem l2PiCoordinateOperator_bound (A : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i))
    (F : Lp ℂ 2 (Measure.pi μ)) : ‖l2PiCoordinateOperator μ i A F‖ ≤ ‖A‖ * ‖F‖ := by
  change ‖(l2PiCoordinateEquiv μ i).symm
    (l2ProductLeftOperator A ((l2PiCoordinateEquiv μ i) F))‖ ≤ _
  rw [LinearIsometryEquiv.norm_map]
  exact ((l2ProductLeftOperator A).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (l2ProductLeftOperator_norm_le A) (norm_nonneg _)).trans_eq
      (congrArg (fun r : ℝ => ‖A‖ * r) ((l2PiCoordinateEquiv μ i).norm_map F)))

theorem l2PiCoordinateOperator_norm_le (A : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i)) :
    ‖l2PiCoordinateOperator μ i A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (l2PiCoordinateOperator_bound μ i A)

theorem l2PiCoordinateOperator_comp (A B : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i)) :
    l2PiCoordinateOperator μ i (A.comp B) =
      (l2PiCoordinateOperator μ i A).comp (l2PiCoordinateOperator μ i B) := by
  apply ContinuousLinearMap.ext
  intro F
  let E := l2PiCoordinateEquiv μ i
  change E.symm (l2ProductLeftOperator (A.comp B) (E F)) =
    E.symm (l2ProductLeftOperator A (E (E.symm (l2ProductLeftOperator B (E F)))))
  rw [LinearIsometryEquiv.apply_symm_apply, l2ProductLeftOperator_comp]
  rfl

theorem l2PiCoordinateOperator_adjoint (A : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i)) :
    (l2PiCoordinateOperator μ i A).adjoint = l2PiCoordinateOperator μ i A.adjoint := by
  apply ContinuousLinearMap.ext
  intro F
  apply ext_inner_left ℂ
  intro G
  rw [ContinuousLinearMap.adjoint_inner_right]
  let E := l2PiCoordinateEquiv μ i
  change ⟪E.symm (l2ProductLeftOperator A (E G)), F⟫_ℂ =
    ⟪G, E.symm (l2ProductLeftOperator A.adjoint (E F))⟫_ℂ
  have hl := E.symm.inner_map_map (l2ProductLeftOperator A (E G)) (E F)
  have hr := E.symm.inner_map_map (E G) (l2ProductLeftOperator A.adjoint (E F))
  simp only [LinearIsometryEquiv.symm_apply_apply] at hl hr
  rw [hl, hr, ← l2ProductLeftOperator_adjoint, ContinuousLinearMap.adjoint_inner_right]

theorem l2PiCoordinateOperator_idempotent (A : Lp ℂ 2 (μ i) →L[ℂ] Lp ℂ 2 (μ i))
    (hA : A.comp A = A) :
    (l2PiCoordinateOperator μ i A).comp (l2PiCoordinateOperator μ i A) =
      l2PiCoordinateOperator μ i A := by
  rw [← l2PiCoordinateOperator_comp, hA]

end
end GinibrePoincare
