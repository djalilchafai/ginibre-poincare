module

public import GinibrePoincare.Analysis.GinibreRadialPhaseWeakTests
public import GinibrePoincare.Analysis.GinibreWeakGradientSupport
public import GinibrePoincare.Analysis.WeakDerivativeMollification

@[expose] public section

/-! # Compact radial weak pairs on the phase-regular set

Collisions are allowed in both supports. Ordinary L² membership and global weak
identities are derived from the actual weighted weak pair and radial value.
-/

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Ordinary L² membership on the compact support implies global membership. -/
theorem memLp_two_volume_of_compact_support_restrict (n : ℕ)
    {V : Type*} [NormedAddCommGroup V] (f : Configuration n → V)
    (hm : AEStronglyMeasurable f volume)
    (hf : MemLp f 2 (volume.restrict (tsupport f))) : MemLp f 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hi : IntegrableOn (fun z => ‖f z‖ ^ 2) (tsupport f) volume :=
    (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  apply hi.integrable_of_forall_notMem_eq_zero
  intro z hz
  simp [image_eq_zero_of_notMem_tsupport hz]

/-- Compact radial values on the phase-regular set belong to ordinary L². -/
theorem ginibre_radial_value_memLp_volume_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ {z | PhaseRegular n z}) :
    MemLp f 2 volume := by
  have hf' := (ginibre_ae_eq_iff_volume n hn _ _).mp hf
  have hm : AEStronglyMeasurable f volume :=
    (AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable u)).congr hf'
  apply memLp_two_volume_of_compact_support_restrict n f hm
  exact (ginibre_radial_value_memLp_compact_phaseRegular n hn u f hf hr (tsupport f) hc hs).ae_eq (ae_restrict_of_ae hf')

/-- Compact representatives of the actual radial weak gradient on the phase-regular set
belong to ordinary L², with collisions permitted. -/
theorem ginibre_radial_gradient_memLp_volume_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hc : HasCompactSupport h) (hs : tsupport h ⊆ {z | PhaseRegular n z}) :
    MemLp h 2 volume := by
  have hh' := (ginibre_ae_eq_iff_volume n hn _ _).mp hh
  have hm : AEStronglyMeasurable h volume :=
    (AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable g)).congr hh'
  apply memLp_two_volume_of_compact_support_restrict n h hm
  exact (ginibre_radial_gradient_memLp_compact_phaseRegular n hn u g hg f hf hr
    (tsupport h) hc hs).ae_eq (ae_restrict_of_ae hh')

/-- Compact radial representatives on the phase-regular set satisfy the ordinary weak-gradient identity
against every smooth compact test on the whole configuration space. -/
theorem ginibre_radial_phaseRegular_weak_gradient_global_identity (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | PhaseRegular n z}) (hhs : tsupport h ⊆ {z | PhaseRegular n z})
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (k : Fin n × Fin 2) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ) :
    (∫ z, h z k * θ z) = -(∫ z, f z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
  obtain ⟨χ, hχ, hsχ, heχ⟩ := exists_smooth_open_cutoff
    (tsupport f ∪ tsupport h) {z : Configuration n | PhaseRegular n z}
    (hfc.union hhc).isClosed (isOpen_phaseRegular n) (Set.union_subset hfs hhs)
  have htest : tsupport (χ * θ) ⊆ {z | PhaseRegular n z} := tsupport_mul_subset_left.trans hsχ
  have he := ginibre_radial_weak_test_phaseRegular n hn u g hg f hf hr k (χ * θ) (hχ.mul hθ) hc.mul_left htest
  have hf' := (ginibre_ae_eq_iff_volume n hn _ _).mp hf
  have hh' := (ginibre_ae_eq_iff_volume n hn _ _).mp hh
  have hl : (∫ z, g z k * (χ * θ) z) = ∫ z, h z k * θ z := by
    apply integral_congr_ae
    filter_upwards [hh'] with z hz
    rw [hz]
    by_cases ht : z ∈ tsupport h
    · have hone : χ z = 1 := (heχ z (Or.inr ht)).eq_of_nhds
      simp only [Pi.mul_apply, hone, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  have hr : (∫ z, u z * fderiv ℝ (χ * θ) z (ginibreCoordinateDirection k)) =
      ∫ z, f z * fderiv ℝ θ z (ginibreCoordinateDirection k) := by
    apply integral_congr_ae
    filter_upwards [hf'] with z hz
    rw [hz]
    by_cases ht : z ∈ tsupport f
    · have hnear := heχ z (Or.inl ht)
      have hone : χ z = 1 := hnear.eq_of_nhds
      have hd : fderiv ℝ χ z = 0 := by rw [hnear.fderiv_eq]; simp
      rw [fderiv_mul (hχ.differentiable (by simp)).differentiableAt
        (hθ.differentiable (by simp)).differentiableAt]
      simp [hone, hd]
    · simp [image_eq_zero_of_notMem_tsupport ht]
  rwa [hl, hr] at he

/-- Genuine smooth convolution of an actual radial weak pair on the phase-regular set has the convolved
weak gradient as its actual classical Euclidean gradient. -/
theorem ginibre_radial_phaseRegular_weak_gradient_mollification (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | PhaseRegular n z}) (hhs : tsupport h ⊆ {z | PhaseRegular n z})
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (φ : Configuration n → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ContDiff ℝ ∞ (φ ⋆[lsmul ℝ ℝ, volume] f) ∧
      ∀ z k, ginibreEuclideanGradient (φ ⋆[lsmul ℝ ℝ, volume] f) z k =
        (φ ⋆[lsmul ℝ ℝ, volume] (fun y => h y k)) z := by
  have hfv : MemLp f 2 volume := ginibre_radial_value_memLp_volume_phaseRegular n hn u f hf hr hfc hfs
  have hfl : LocallyIntegrable f volume := hfv.locallyIntegrable (by norm_num)
  refine ⟨hφc.contDiff_convolution_left _ hφ hfl, ?_⟩
  intro z k
  rw [ginibreEuclideanGradient_coordinate]
  exact weakDirectionalDerivative_convolution volume f (fun y => h y k) φ
    (ginibreCoordinateDirection k) hfl hφ hφc
    (ginibre_radial_phaseRegular_weak_gradient_global_identity n hn u g hg f h hf hh hfc hhc hfs hhs hr k) z


end
end GinibrePoincare
