module

public import GinibrePoincare.Analysis.CorrespondenceCollisionDensity

@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Quadratic density vanishing makes a compact collision tube have fourth-order
mass under the literal normalized Ginibre law. -/
theorem correspondenceCollision_compact_tube_mass {n : ℕ} (hn : 0 < n)
    (p : VandermondePair n) (K : Set (Configuration n)) (hK : IsCompact K) :
    ∃ D : ℝ≥0∞, D ≠ ⊤ ∧ ∀ r : ℝ, 0 ≤ r →
      ginibreMeasure n {z | z ∈ K ∧ ‖z p.val.1 - z p.val.2‖ ≤ r} ≤
        D * ENNReal.ofReal r ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := correspondenceCollision_density_bound_compact p K hK
  obtain ⟨V, hV, hVol⟩ := correspondenceCollision_compact_tube_volume
    p.val.1 p.val.2 (ne_of_gt p.property) K hK
  let D := (ginibreNormalizingMass n)⁻¹ * ENNReal.ofReal C * V
  refine ⟨D, ?_, ?_⟩
  · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.inv_ne_top.mpr (ginibreNormalizingMass_pos hn).ne') (by simp)) hV
  · intro r hr
    let T : Set (Configuration n) := {z | z ∈ K ∧ ‖z p.val.1 - z p.val.2‖ ≤ r}
    have hc : Continuous (fun z : Configuration n => ‖z p.val.1 - z p.val.2‖) := by fun_prop
    have hT : MeasurableSet T := hK.measurableSet.inter
      (isClosed_le hc continuous_const).measurableSet
    rw [ginibreMeasure_eq_real_withDensity hn, Measure.smul_apply,
      withDensity_apply _ hT]
    have hb : (∫⁻ z in T, ENNReal.ofReal (ginibreLebesgueDensityReal n z)) ≤
        ∫⁻ _ in T, ENNReal.ofReal (C * r ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hT] with z hz
      apply ENNReal.ofReal_le_ofReal
      exact (hC z hz.1).trans
        (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg _) hr).mpr hz.2) hC0)
    calc
      _ ≤ (ginibreNormalizingMass n)⁻¹ * ∫⁻ _ in T, ENNReal.ofReal (C * r ^ 2) :=
        mul_le_mul le_rfl hb zero_le zero_le
      _ = (ginibreNormalizingMass n)⁻¹ * ENNReal.ofReal C *
          ENNReal.ofReal r ^ 2 * volume T := by
        rw [lintegral_const, Measure.restrict_apply_univ,
          ENNReal.ofReal_mul hC0, ENNReal.ofReal_pow hr]
        ring
      _ ≤ (ginibreNormalizingMass n)⁻¹ * ENNReal.ofReal C *
          ENNReal.ofReal r ^ 2 * (V * ENNReal.ofReal r ^ 2) :=
        mul_le_mul le_rfl (hVol r) zero_le zero_le
      _ = D * ENNReal.ofReal r ^ 4 := by dsimp [D]; ring

end
end GinibrePoincare

#print axioms GinibrePoincare.correspondenceCollision_compact_tube_mass
