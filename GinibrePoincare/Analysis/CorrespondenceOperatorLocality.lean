module
public import GinibrePoincare.Analysis.CorrespondenceOperatorSmoothIdentification
@[expose] public section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Strong locality of the literal weighted Euclidean Dirichlet integral:
if the second observable is locally constant on the first one's support,
the mixed energy is zero. -/
theorem correspondenceOperator_dirichlet_strong_locality {n : ℕ}
    (f g : Configuration n → ℝ)
    (hlocal : ∀ z ∈ tsupport f, ∃ c : ℝ, g =ᶠ[𝓝 z] (fun _ => c)) :
    (1/(n : ℝ))*(∫ z, inner ℝ (ginibreEuclideanGradient f z)
      (ginibreEuclideanGradient g z) ∂ginibreMeasure n)=0 := by
  have he : ∀ z, inner ℝ (ginibreEuclideanGradient f z)
      (ginibreEuclideanGradient g z)=0 := by
    intro z
    by_cases hz : z∈tsupport f
    · obtain ⟨c, hc⟩ := hlocal z hz
      have hd : fderiv ℝ g z=0 := by rw [hc.fderiv_eq]; simp
      have hg : ginibreEuclideanGradient g z=0 := by
        ext k
        simp [ginibreEuclideanGradient, hd]
      rw [hg, inner_zero_right]
    · have hf : ginibreEuclideanGradient f z=0 := by
        ext k
        simp [ginibreEuclideanGradient, fderiv_of_notMem_tsupport ℝ hz]
      rw [hf, inner_zero_left]
  simp only [he, integral_zero, mul_zero]

/-- A genuine ordinary weak gradient vanishes where its observable is
constant on an open set; this is derived from distributional testing. -/
theorem correspondenceOperator_weak_gradient_zero_on_constant_open (n : ℕ) (hn : 0<n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (U : Set (Configuration n)) (hU : IsOpen U) (hs : U ⊆ {z | CollisionFree z})
    (c : ℝ) (hc : ∀ z∈U, u z=c) :
    ∀ᵐ z ∂ginibreMeasure n, z∈U → g z=0 := by
  have hac : ginibreMeasure n ≪ (volume : Measure (Configuration n)) := by
    rw [ginibreMeasure_eq_real_withDensity hn]
    exact (withDensity_absolutelyContinuous _ _).smul_left _
  have hz (k : Fin n × Fin 2) : ∀ᵐ z ∂volume, z∈U → g z k=0 := by
    apply hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hu.2.1 k).mono_set hs)
    intro θ hθ hθc hθs
    have hds : tsupport (fun z => fderiv ℝ θ z (ginibreCoordinateDirection k)) ⊆ U :=
      (tsupport_fderiv_apply_subset ℝ _).trans hθs
    have he : (fun z => u z*fderiv ℝ θ z (ginibreCoordinateDirection k)) =
        fun z => c*fderiv ℝ θ z (ginibreCoordinateDirection k) := by
      funext z
      by_cases hz : z∈U
      · rw [hc z hz]
      · have hz' : z∉tsupport (fun y => fderiv ℝ θ y (ginibreCoordinateDirection k)) :=
          fun hh => hz (hds hh)
        have hd := image_eq_zero_of_notMem_tsupport hz'
        simp [hd]
    have hdz : (∫ z, fderiv ℝ θ z (ginibreCoordinateDirection k))=0 := by
      rcases k with ⟨j, k⟩
      fin_cases k
      · exact integral_fderiv_configuration_real_eq_zero θ (hθ.of_le (by simp)) hθc j
      · exact integral_fderiv_configuration_imag_eq_zero θ (hθ.of_le (by simp)) hθc j
    have hw := hu.2.2 k θ hθ hθc (hθs.trans hs)
    rw [he, integral_const_mul, hdz, mul_zero, neg_zero] at hw
    simpa only [smul_eq_mul, mul_comm] using hw
  have hAll : ∀ᵐ z ∂volume, ∀ k : Fin n × Fin 2, z∈U → g z k=0 :=
    (ae_all_iff.mpr hz)
  filter_upwards [hac.ae_le hAll] with z hz
  intro hzu
  ext k
  simpa using hz k hzu

/-- Strong locality on the entire unrestricted weak-H¹ form domain, with
ordinary weak gradients, rather than only the differential test core. -/
theorem correspondenceOperator_weak_dirichlet_strong_locality (n : ℕ) (hn : 0<n)
    (u v : GinibreFullValueL2 n) (g h : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g) (hv : IsGinibreDistributionalGradient n v h)
    (U : Set (Configuration n)) (hU : IsOpen U) (hs : U ⊆ {z | CollisionFree z})
    (hus : tsupport (u : Configuration n → ℝ) ⊆ U)
    (c : ℝ) (hvc : ∀ z∈U, v z=c) :
    (1/(n : ℝ))*inner ℝ g h=0 := by
  have hzero := correspondenceOperator_weak_gradient_zero_on_constant_open n hn v h hv U hU hs c hvc
  let V := {z : Configuration n | CollisionFree z} ∩ (tsupport (u : Configuration n → ℝ))ᶜ
  have hV : IsOpen V := (isOpen_collisionFree n).inter (isClosed_tsupport _).isOpen_compl
  have hgu := correspondenceOperator_weak_gradient_zero_on_constant_open n hn u g hu V hV
    Set.inter_subset_left 0 (fun z hz => image_eq_zero_of_notMem_tsupport hz.2)
  rw [L2.inner_def]
  have hi : (∫ z, inner ℝ (g z) (h z) ∂ginibreMeasure n)=0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero, hgu, ginibre_ae_collisionFree n hn] with z hhz hgz hcf
    change inner ℝ (g z) (h z)=0
    by_cases hz : z∈U
    · rw [hhz hz, inner_zero_right]
    · have hout : z∉tsupport (u : Configuration n → ℝ) := fun hh => hz (hus hh)
      rw [hgz ⟨hcf, hout⟩, inner_zero_left]
  rw [hi, mul_zero]

#print axioms correspondenceOperator_weak_gradient_zero_on_constant_open
#print axioms correspondenceOperator_weak_dirichlet_strong_locality
#print axioms correspondenceOperator_dirichlet_strong_locality
end
end GinibrePoincare
