module
public import GinibrePoincare.Analysis.CorrespondenceOperatorSmoothCore
public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingGreen
@[expose] public section
namespace GinibrePoincare
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option backward.isDefEq.respectTransparency false
/-- The actual weighted real L² gradient of a smooth collision-free core observable. -/
def correspondenceOperator_ginibreFullCoreGradient {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) : GinibreFullGradientL2 n :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).2.toLp (ginibreEuclideanGradient f)

theorem correspondenceOperator_ginibreFullCoreGradient_ae {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) :
    (correspondenceOperator_ginibreFullCoreGradient hn f hf : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] ginibreEuclideanGradient f :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).2.coeFn_toLp

/-- Concrete real L² class of the smooth core pregenerator. -/
def correspondenceOperator_ginibreFullCorePregenerator {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) : GinibreFullValueL2 n := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (((correspondenceOperator_pregenerator_contDiff hn f hf.1 hf.2.2).continuous).memLp_of_hasCompactSupport
    (hasCompactSupport_ginibrePregenerator hf.2.1)).toLp (ginibrePregenerator n f)

theorem correspondenceOperator_ginibreFullCorePregenerator_ae {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) :
    (correspondenceOperator_ginibreFullCorePregenerator hn f hf : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      ginibrePregenerator n f := by
  let := ginibreMeasure_isProbabilityMeasure hn
  exact (((correspondenceOperator_pregenerator_contDiff hn f hf.1 hf.2.2).continuous).memLp_of_hasCompactSupport
    (hasCompactSupport_ginibrePregenerator hf.2.1)).coeFn_toLp

/-- Exact integration by parts between every ordinary Ginibre weak pair and
an actual collision-free smooth core observable, with normalization `1/n`. -/
theorem correspondenceOperator_ginibreFullGenerator_weak_core_green {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) :
    (1 / (n : ℝ)) * inner ℝ g (correspondenceOperator_ginibreFullCoreGradient hn f hf) =
      -inner ℝ u (correspondenceOperator_ginibreFullCorePregenerator hn f hf) := by
  let := ginibreMeasure_isProbabilityMeasure hn
  let θ (k : Fin n × Fin 2) : Configuration n → ℝ := fun z =>
    ginibreLebesgueDensityReal n z * fderiv ℝ f z (ginibreCoordinateDirection k)
  let δ (k : Fin n × Fin 2) : Configuration n → ℝ := fun z =>
    fderiv ℝ (θ k) z (ginibreCoordinateDirection k) / ginibreLebesgueDensityReal n z
  have hθ (k) : ContDiff ℝ ∞ (θ k) := (contDiff_ginibreLebesgueDensityReal n).mul (((hf.1.contDiff_fderiv_apply (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)))
  have hcθ (k) : HasCompactSupport (θ k) := (hf.2.1.fderiv_apply ℝ _).mul_left
  have hfs : tsupport f ⊆ {z | CollisionFree z} := fun z hz =>
    hf.2.2 hz
  have hsθ (k) : tsupport (θ k) ⊆ {z | CollisionFree z} :=
    (tsupport_mul_subset_right.trans (tsupport_fderiv_apply_subset ℝ _)).trans hfs
  have hδ (k) : MemLp (δ k) 2 (ginibreMeasure n) := by
    have hc : HasCompactSupport (fun z => fderiv ℝ (θ k) z (ginibreCoordinateDirection k)) :=
      (hcθ k).fderiv_apply ℝ _
    have hcont : Continuous (fun z => fderiv ℝ (θ k) z (ginibreCoordinateDirection k)) :=
      ((hθ k).continuous_fderiv (by simp)).clm_apply continuous_const
    have hs := (tsupport_fderiv_apply_subset ℝ (ginibreCoordinateDirection k)).trans (hsθ k)
    have hdiv := collisionFree_test_div_density n hn _ hcont hc hs
    exact hdiv.1.memLp_of_hasCompactSupport hdiv.2
  have hdf (k) : MemLp (fun z => fderiv ℝ f z (ginibreCoordinateDirection k)) 2 (ginibreMeasure n) := by
    have hcont : Continuous (fun z => fderiv ℝ f z (ginibreCoordinateDirection k)) :=
      (hf.1.continuous_fderiv (by simp)).clm_apply continuous_const
    exact hcont.memLp_of_hasCompactSupport (hf.2.1.fderiv_apply ℝ _)
  have hgk (k) : MemLp (fun z => g z k) 2 (ginibreMeasure n) := by
    let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ := PiLp.proj 2 (fun _ => ℝ) k
    exact P.comp_memLp g
  have hInt (k) : Integrable (fun z => g z k * fderiv ℝ f z (ginibreCoordinateDirection k))
      (ginibreMeasure n) := (hgk k).integrable_mul (hdf k)
  have hIntδ (k) : Integrable (fun z => u z * δ k z) (ginibreMeasure n) :=
    (Lp.memLp u).integrable_mul (hδ k)
  have hpair (k) : (∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n) =
      -(∫ z, u z * δ k z ∂ginibreMeasure n) := by
    have h := ginibreFull_distributional_density_pairing n hn u g hu k (θ k) (hθ k) (hcθ k) (hsθ k)
    have he : (∫ z, g z k * (θ k z / ginibreLebesgueDensityReal n z) ∂ginibreMeasure n) =
        ∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n := by
      apply integral_congr_ae
      filter_upwards [ginibreFull_core_flux_div_density_ae hn f (ginibreCoordinateDirection k)] with z hz
      rw [hz]
    rw [he] at h
    exact h
  have hinner : inner ℝ g (correspondenceOperator_ginibreFullCoreGradient hn f hf) =
      ∑ k : Fin n × Fin 2, ∫ z, g z k * fderiv ℝ f z (ginibreCoordinateDirection k) ∂ginibreMeasure n := by
    rw [L2.inner_def, ← integral_finsetSum Finset.univ (fun k _ => hInt k)]
    apply integral_congr_ae
    filter_upwards [correspondenceOperator_ginibreFullCoreGradient_ae hn f hf] with z hz
    rw [hz, PiLp.inner_apply]
    apply Finset.sum_congr rfl
    intro k hk
    rw [ginibreEuclideanGradient_coordinate]
    change fderiv ℝ f z (ginibreCoordinateDirection k) * g z k = _
    ring
  rw [hinner]
  simp_rw [hpair]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum Finset.univ (fun k _ => hIntδ k)]
  have hsum : (fun z => ∑ k : Fin n × Fin 2, u z * δ k z) =
      fun z => u z * ∑ k : Fin n × Fin 2, δ k z := by
    funext z
    exact (Finset.mul_sum _ _ _).symm
  rw [hsum]
  rw [mul_neg, ← integral_const_mul]
  rw [L2.inner_def]
  congr 1
  apply integral_congr_ae
  filter_upwards [ginibreLocalWeak_generator_divergence_ae hn f hf.1,
    correspondenceOperator_ginibreFullCorePregenerator_ae hn f hf] with z hdiv hgen
  change (1 / (n : ℝ)) * (u z * ∑ k : Fin n × Fin 2, δ k z) =
    (correspondenceOperator_ginibreFullCorePregenerator hn f hf) z * u z
  rw [hgen]
  change (1 / (n : ℝ)) * (∑ k : Fin n × Fin 2, δ k z) = ginibrePregenerator n f z at hdiv
  rw [mul_left_comm, hdiv]
  ring



def correspondenceOperator_ginibreFullCoreValue {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) : GinibreFullValueL2 n :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).1.toLp f

theorem correspondenceOperator_ginibreFullCoreValue_ae {n : ℕ} (hn : 0 < n) (f : Configuration n → ℝ)
    (hf : (ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ {z | CollisionFree z})) :
    (correspondenceOperator_ginibreFullCoreValue hn f hf : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f :=
  (ginibreFull_smoothCompact_memLp n hn f hf.1 hf.2.1).1.coeFn_toLp


#print axioms correspondenceOperator_ginibreFullGenerator_weak_core_green
end
end GinibrePoincare
