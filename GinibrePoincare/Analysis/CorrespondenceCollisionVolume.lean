module

public import GinibrePoincare.Analysis.CorrespondenceCollisionCoordinates

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- A compact collision tube has quadratic Lebesgue volume, uniformly in its width. -/
theorem correspondenceCollision_compact_tube_volume {n : ℕ} (j k : Fin n) (hjk : k ≠ j)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ r : ℝ,
      volume {z : Configuration n | z ∈ K ∧ ‖z j - z k‖ ≤ r} ≤
        C * ENNReal.ofReal r ^ 2 := by
  classical
  let L : Set ({i : Fin n // i ≠ j} → ℂ) :=
    (fun z : Configuration n => fun i : {i : Fin n // i ≠ j} => z i.val) '' K
  have hL : IsCompact L := hK.image (by fun_prop)
  refine ⟨volume L * NNReal.pi, ENNReal.mul_ne_top hL.measure_ne_top (by simp), ?_⟩
  intro r
  let B : Set (ℂ × ({i : Fin n // i ≠ j} → ℂ)) :=
    {p | p.2 ∈ L ∧ ‖p.1 - p.2 ⟨k, hjk⟩‖ ≤ r}
  have hc : Continuous (fun p : ℂ × ({i : Fin n // i ≠ j} → ℂ) =>
      ‖p.1 - p.2 ⟨k, hjk⟩‖) := by fun_prop
  have hB : MeasurableSet B := (hL.measurableSet.preimage measurable_snd).inter
    (isClosed_le hc continuous_const).measurableSet
  have hsub : {z : Configuration n | z ∈ K ∧ ‖z j - z k‖ ≤ r} ⊆
      correspondenceCollisionSplit j ⁻¹' B := by
    intro z hz
    rw [Set.mem_preimage, correspondenceCollisionSplit_apply]
    exact ⟨⟨z, hz.1, rfl⟩, hz.2⟩
  calc
    _ ≤ volume (correspondenceCollisionSplit j ⁻¹' B) := measure_mono hsub
    _ = volume B := (correspondenceCollisionSplit_volume j).measure_preimage hB.nullMeasurableSet
    _ = (volume L * NNReal.pi) * ENNReal.ofReal r ^ 2 := by
      rw [Measure.volume_eq_prod, Measure.prod_apply_symm hB]
      have hfib (y : {i : Fin n // i ≠ j} → ℂ) :
          ((fun x : ℂ => (x, y)) ⁻¹' B) =
          if y ∈ L then Metric.closedBall (y ⟨k, hjk⟩) r else ∅ := by
        ext x
        by_cases hy : y ∈ L <;> simp [B, hy, Metric.mem_closedBall, dist_eq_norm]
      simp_rw [hfib]
      simp only [apply_ite volume, Complex.volume_closedBall, measure_empty]
      change (∫⁻ y, L.indicator (fun _ => ENNReal.ofReal r ^ 2 * NNReal.pi) y) = _
      rw [lintegral_indicator hL.measurableSet, lintegral_const]
      rw [Measure.restrict_apply_univ]
      ring

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceCollision_compact_tube_volume
