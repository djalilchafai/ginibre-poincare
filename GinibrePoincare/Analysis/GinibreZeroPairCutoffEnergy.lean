module

public import GinibrePoincare.Analysis.GinibreZeroPairAvoidance

@[expose] public section

/-! # Vanishing energy of the actual symmetric zero-pair cutoffs

The fixed inverse-radius domination is integrable on every compact set under the
concrete Ginibre measure. Dominated convergence proves vanishing cutoff energy,
including at compact sets meeting the exceptional simultaneous-zero locus.
-/

open MeasureTheory Filter
open scoped Topology BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- The phase-regular set has full measure for the concrete Ginibre law. -/
theorem ginibre_ae_phaseRegular (n : ℕ) (hn : 0 < n) :
    ∀ᵐ z ∂ginibreMeasure n, PhaseRegular n z := by
  have hcf : ∀ᵐ z ∂(volume : Measure (Configuration n)), CollisionFree z := by
    rw [ae_iff]
    have he : {z : Configuration n | ¬ CollisionFree z} = collisionSet n := by
      ext z; simp [collisionFree_iff_not_mem_collisionSet]
    rw [he]
    exact configurationVolume_collisionSet hn
  obtain ⟨c, hc, hm⟩ := ginibreMeasure_le_finite_smul_volume n hn
  filter_upwards [(Measure.absolutelyContinuous_of_le_smul hm).ae_le hcf] with z hz
  refine ⟨fun _ => 1, fun _ => by simp, ?_⟩
  have he : coordinatePhase (fun _ : Fin n => (1 : ℂ)) z = z := by
    ext i; simp [coordinatePhase]
  rw [he]
  exact hz

/-- The sum of the actual inverse pair radii is integrable on every compact set. -/
theorem ginibre_inverse_pair_radius_sum_integrableOn_compact (n : ℕ) (hn : 0 < n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    IntegrableOn (fun z => ∑ p : DistinctCoordinatePair n,
      (ginibrePairRadiusSq p.val.1 p.val.2 z)⁻¹) K (ginibreMeasure n) := by
  classical
  apply integrable_finsetSum
  intro p _
  exact ginibre_pair_radius_inv_integrableOn_compact n hn p.val.1 p.val.2 p.property K hK

/-- The actual cutoff energy tends to zero on every compact set, with no
restriction excluding simultaneous coordinate zeroes. -/
theorem ginibreZeroPairAvoidanceCutoff_compact_energy_tendsto (n : ℕ) (hn : 0 < n)
    (K : Set (Configuration n)) (hK : IsCompact K) :
    Tendsto (fun m => ∫ z in K,
      ‖ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC0, hC⟩ := ginibreZeroPairAvoidanceCutoff_gradient_inverse_bound
  have hi := (ginibre_inverse_pair_radius_sum_integrableOn_compact n hn K hK).const_mul ((Fintype.card (DistinctCoordinatePair n) : ℝ) * C)
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun z => (Fintype.card (DistinctCoordinatePair n) : ℝ) * C *
      ∑ p : DistinctCoordinatePair n, (ginibrePairRadiusSq p.val.1 p.val.2 z)⁻¹)
    (fun m => (((continuous_ginibreEuclideanGradient _
      (ginibreZeroPairAvoidanceCutoff_smooth n m)).norm.pow 2).aestronglyMeasurable))
    hi
    (fun m => ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hC n m z))
    ?_
  · simpa using ht
  · filter_upwards [ae_restrict_of_ae (ginibre_ae_phaseRegular n hn)] with z hz
    have he : (fun m => ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z) =ᶠ[atTop]
        (fun _ => 0) :=
      (ginibreZeroPairAvoidanceCutoff_eventually_one_gradient_zero n hn z hz).mono (fun m hm => hm.2)
    have ht' : Tendsto (fun m => ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z)
        atTop (𝓝 0) := tendsto_const_nhds.congr' he.symm
    simpa using ht'.norm.pow 2

/-- Multiplying the cutoff gradient by any bounded measurable value still has
vanishing actual weighted energy on every compact set. -/
theorem ginibreZeroPairAvoidanceCutoff_bounded_compact_energy_tendsto
    (n : ℕ) (hn : 0 < n) (K : Set (Configuration n)) (hK : IsCompact K)
    (f : Configuration n → ℝ) (hf : AEStronglyMeasurable f (ginibreMeasure n))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Tendsto (fun m => ∫ z in K,
      ‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC0, hC⟩ := ginibreZeroPairAvoidanceCutoff_gradient_inverse_bound
  have hi := ((ginibre_inverse_pair_radius_sum_integrableOn_compact n hn K hK).const_mul
    ((Fintype.card (DistinctCoordinatePair n) : ℝ) * C)).const_mul (A ^ 2)
  have ht := tendsto_integral_of_dominated_convergence (f := fun _ => (0 : ℝ))
    (fun z => A ^ 2 * ((Fintype.card (DistinctCoordinatePair n) : ℝ) * C *
      ∑ p : DistinctCoordinatePair n, (ginibrePairRadiusSq p.val.1 p.val.2 z)⁻¹))
    (fun m => ((hf.smul (continuous_ginibreEuclideanGradient _
      (ginibreZeroPairAvoidanceCutoff_smooth n m)).aestronglyMeasurable).norm.pow 2).restrict)
    hi
    (fun m => ae_of_all _ (fun z => by
      change ‖‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, mul_pow]
      have ha : ‖f z‖ ^ 2 ≤ A ^ 2 := by nlinarith [norm_nonneg (f z), hA z]
      exact mul_le_mul ha (hC n m z) (sq_nonneg _) (sq_nonneg A)))
    ?_
  · simpa [mul_assoc] using ht
  · filter_upwards [ae_restrict_of_ae (ginibre_ae_phaseRegular n hn)] with z hz
    have he : (fun m => ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z) =ᶠ[atTop]
        (fun _ => 0) :=
      (ginibreZeroPairAvoidanceCutoff_eventually_one_gradient_zero n hn z hz).mono (fun m hm => hm.2)
    have ht' : Tendsto (fun m => ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z)
        atTop (𝓝 0) := tendsto_const_nhds.congr' he.symm
    simpa using (ht'.const_smul (f z)).norm.pow 2

/-- The cutoff-gradient error of a bounded compact value belongs to actual
Ginibre L² at every scale, including when its support meets simultaneous zeroes. -/
theorem ginibreZeroPairAvoidanceCutoff_bounded_gradient_memLp
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (hc : HasCompactSupport f)
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) (m : ℕ) :
    MemLp (fun z => f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z)
      2 (ginibreMeasure n) := by
  classical
  have hm := hf.smul (continuous_ginibreEuclideanGradient _
    (ginibreZeroPairAvoidanceCutoff_smooth n m)).aestronglyMeasurable
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  obtain ⟨C, hC0, hC⟩ := ginibreZeroPairAvoidanceCutoff_gradient_inverse_bound
  have hi := ((ginibre_inverse_pair_radius_sum_integrableOn_compact n hn (tsupport f) hc).const_mul ((Fintype.card (DistinctCoordinatePair n) : ℝ) * C)).const_mul (A ^ 2)
  have hb : IntegrableOn (fun z =>
      ‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2)
      (tsupport f) (ginibreMeasure n) := by
    apply hi.mono' (hm.norm.pow 2).restrict
    apply ae_of_all
    intro z
    change ‖‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, mul_pow]
    have ha : ‖f z‖ ^ 2 ≤ A ^ 2 := by nlinarith [norm_nonneg (f z), hA z]
    exact mul_le_mul ha (hC n m z) (sq_nonneg _) (sq_nonneg A)
  apply hb.integrable_of_forall_notMem_eq_zero
  intro z hz
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- The actual cutoff-gradient error tends to zero globally for bounded compact
values. No interior-support or independently supplied energy premise is required. -/
theorem ginibreZeroPairAvoidanceCutoff_bounded_gradient_energy_tendsto
    (n : ℕ) (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : AEStronglyMeasurable f (ginibreMeasure n)) (hc : HasCompactSupport f)
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Tendsto (fun m => ∫ z,
      ‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) atTop (𝓝 0) := by
  have he (m : ℕ) : (∫ z in tsupport f,
      ‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n) = ∫ z,
      ‖f z • ginibreEuclideanGradient (ginibreZeroPairAvoidanceCutoff n m) z‖ ^ 2
        ∂ginibreMeasure n := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro z hz
    simp [image_eq_zero_of_notMem_tsupport hz]
  simpa only [he] using ginibreZeroPairAvoidanceCutoff_bounded_compact_energy_tendsto
    n hn (tsupport f) hc f hf A hA0 hA

end
end GinibrePoincare
