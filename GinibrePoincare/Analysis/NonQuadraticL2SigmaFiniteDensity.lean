module

public import GinibrePoincare.Analysis.NonQuadraticL2ProductDensity

@[expose] public section

/-! # Actual tensor density for σ-finite factors
Finite measurable rectangle exhaustion removes any finite-mass restriction
from the L² tensor realization. This applies directly to planar Lebesgue space. -/
open MeasureTheory MeasureTheory.Measure Set
open scoped InnerProductSpace TensorProduct ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {μ : Measure X} {ν : Measure Y} [SigmaFinite μ] [SigmaFinite ν]

private theorem product_integrable_ae_zero_of_rectangles
    (F : X × Y → ℂ) (hFi : Integrable F (μ.prod ν))
    (hrect : ∀ s t, MeasurableSet s → MeasurableSet t → (∫ z in s ×ˢ t, F z ∂μ.prod ν) = 0) :
    F =ᵐ[μ.prod ν] 0 := by
  have hvm : (μ.prod ν).withDensityᵥ F = (0 : VectorMeasure (X × Y) ℂ) := by
    apply VectorMeasure.ext_of_generateFrom _ _ generateFrom_prod.symm isPiSystem_prod
    · rw [withDensityᵥ_apply hFi MeasurableSet.univ]
      simpa only [univ_prod_univ, setIntegral_univ, VectorMeasure.zero_apply] using
        hrect univ univ MeasurableSet.univ MeasurableSet.univ
    · rintro _ ⟨s, hs, t, ht, rfl⟩
      rw [withDensityᵥ_apply hFi (hs.prod ht), hrect s t hs ht]
      rfl
  apply hFi.ae_eq_of_withDensityᵥ_eq (integrable_zero _ _ (μ.prod ν))
  rw [withDensityᵥ_zero]
  exact hvm

/-- Finite-support indicator vectors under σ-finite factors. -/
def l2FiniteIndicatorVector (s : Set X) (hs : MeasurableSet s) (hfin : μ s < ∞) : Lp ℂ 2 μ :=
  (memLp_indicator_const (μ := μ) 2 hs (1 : ℂ) (Or.inr hfin.ne)).toLp _

private theorem l2FiniteIndicatorVector_coeFn (s : Set X) (hs : MeasurableSet s) (hfin : μ s < ∞) :
    l2FiniteIndicatorVector s hs hfin =ᵐ[μ] s.indicator (fun _ => (1 : ℂ)) :=
  (memLp_indicator_const (μ := μ) 2 hs (1 : ℂ) (Or.inr hfin.ne)).coeFn_toLp

private theorem l2Product_finite_indicator_rectangle (s : Set X) (t : Set Y)
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hfs : μ s < ∞) (hft : ν t < ∞) :
    l2ProductVector (l2FiniteIndicatorVector s hs hfs) (l2FiniteIndicatorVector t ht hft) =ᵐ[μ.prod ν]
      (s ×ˢ t).indicator (fun _ => (1 : ℂ)) := by
  have hsu := (quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae_eq_comp (l2FiniteIndicatorVector_coeFn s hs hfs)
  have htv := (quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae_eq_comp (l2FiniteIndicatorVector_coeFn t ht hft)
  filter_upwards [l2ProductVector_coeFn (l2FiniteIndicatorVector s hs hfs) (l2FiniteIndicatorVector t ht hft), hsu, htv]
    with z hz hz1 hz2
  change (l2FiniteIndicatorVector s hs hfs) z.1 = s.indicator (fun _ => (1 : ℂ)) z.1 at hz1
  change (l2FiniteIndicatorVector t ht hft) z.2 = t.indicator (fun _ => (1 : ℂ)) z.2 at hz2
  rw [hz, hz1, hz2]
  by_cases hx : z.1 ∈ s <;> by_cases hy : z.2 ∈ t <;> simp [hx, hy]

/-- Actual pure tensors separate the full σ-finite product L² space. -/
theorem l2Product_eq_zero_of_inner_pure_tensors_sigmaFinite (F : Lp ℂ 2 (μ.prod ν))
    (horth : ∀ u : Lp ℂ 2 μ, ∀ v : Lp ℂ 2 ν, ⟪l2ProductVector u v, F⟫_ℂ = 0) : F = 0 := by
  have hrect (s : Set X) (t : Set Y) (hs : MeasurableSet s) (ht : MeasurableSet t)
      (hfs : μ s < ∞) (hft : ν t < ∞) : (∫ z in s ×ˢ t, F z ∂μ.prod ν) = 0 := by
    have hi := horth (l2FiniteIndicatorVector s hs hfs) (l2FiniteIndicatorVector t ht hft)
    rw [L2.inner_def] at hi
    have he : (∫ z, ⟪l2ProductVector (l2FiniteIndicatorVector s hs hfs)
        (l2FiniteIndicatorVector t ht hft) z, F z⟫_ℂ ∂μ.prod ν) =
        ∫ z, (s ×ˢ t).indicator (fun z => F z) z ∂μ.prod ν := by
      apply integral_congr_ae
      filter_upwards [l2Product_finite_indicator_rectangle s t hs ht hfs hft] with z hz
      rw [hz]
      by_cases hzst : z ∈ s ×ˢ t <;> simp [hzst, RCLike.inner_apply]
    rw [he, integral_indicator (hs.prod ht)] at hi
    exact hi
  have hlocal (n m : ℕ) :
      ((spanningSets μ n) ×ˢ (spanningSets ν m)).indicator (fun z => F z) =ᵐ[μ.prod ν] 0 := by
    let R := (spanningSets μ n) ×ˢ (spanningSets ν m)
    have hRm : MeasurableSet R := (measurableSet_spanningSets μ n).prod (measurableSet_spanningSets ν m)
    have hRfin : (μ.prod ν) R < ∞ := by
      rw [prod_prod]
      exact ENNReal.mul_lt_top (measure_spanningSets_lt_top μ n) (measure_spanningSets_lt_top ν m)
    letI : IsFiniteMeasure ((μ.prod ν).restrict R) := ⟨by rw [Measure.restrict_apply_univ]; exact hRfin⟩
    have hFi : Integrable (R.indicator (fun z => F z)) (μ.prod ν) :=
      (integrable_indicator_iff hRm).2 (((Lp.memLp F).restrict R).integrable (by norm_num))
    apply product_integrable_ae_zero_of_rectangles _ hFi
    intro s t hs ht
    rw [setIntegral_indicator hRm, prod_inter_prod]
    exact hrect _ _ (hs.inter (measurableSet_spanningSets μ n))
      (ht.inter (measurableSet_spanningSets ν m))
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top μ n))
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top ν m))
  have hall : ∀ᵐ z ∂μ.prod ν, ∀ n m : ℕ,
      ((spanningSets μ n) ×ˢ (spanningSets ν m)).indicator (fun z => F z) z = 0 := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro m
    exact hlocal n m
  have hzero : F =ᵐ[μ.prod ν] (0 : X × Y → ℂ) := by
    filter_upwards [hall] with z hz
    obtain ⟨n, hn⟩ := mem_iUnion.mp (show z.1 ∈ ⋃ n, spanningSets μ n by rw [iUnion_spanningSets]; trivial)
    obtain ⟨m, hm⟩ := mem_iUnion.mp (show z.2 ∈ ⋃ m, spanningSets ν m by rw [iUnion_spanningSets]; trivial)
    simpa only [Pi.zero_apply, indicator_of_mem (show z ∈ spanningSets μ n ×ˢ spanningSets ν m from ⟨hn, hm⟩)] using hz n m
  apply Lp.ext
  exact hzero.trans (Lp.coeFn_zero ℂ 2 (μ.prod ν)).symm
/-- The completed Hilbert tensor fills the actual σ-finite-product L² space.
Surjectivity follows from proved rectangle separation, not a density axiom. -/
theorem l2ProductCompletedTensorIsometry_surjective_sigmaFinite :
    Function.Surjective (l2ProductCompletedTensorIsometry (μ := μ) (ν := ν)) := by
  let e := l2ProductCompletedTensorIsometry (μ := μ) (ν := ν)
  let K : ClosedSubmodule ℂ (Lp ℂ 2 (μ.prod ν)) :=
    ⟨e.toLinearMap.range, e.isometry.isClosedEmbedding.isClosed_range⟩
  have hKo : K.toSubmoduleᗮ = ⊥ := by
    apply le_antisymm
    · intro F hF
      change F = 0
      apply l2Product_eq_zero_of_inner_pure_tensors_sigmaFinite
      intro u v
      have hp : l2ProductVector u v ∈ K := by
        refine ⟨((u ⊗ₜ[ℂ] v : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
          UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)), ?_⟩
        change l2ProductTensorIsometry.toContinuousLinearMap.fromCompletion
          ((u ⊗ₜ[ℂ] v : Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) :
            UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν)) = _
        rw [ContinuousLinearMap.fromCompletion_apply_coe]
        rfl
      exact inner_eq_zero_symm.mp ((Submodule.mem_orthogonal' _ _).mp hF _ hp)
    · exact bot_le

  letI : CompleteSpace (Lp ℂ 2 (μ.prod ν)) := inferInstance
  letI : CompleteSpace K.toSubmodule := K.isClosed'.completeSpace_coe
  letI : K.toSubmodule.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K.toSubmodule
  have hKt : K.toSubmodule = ⊤ := (Submodule.orthogonal_eq_bot_iff).mp hKo
  intro F
  have hF : F ∈ K.toSubmodule := by rw [hKt]; trivial
  exact hF

/-- Actual product-measure L² is isometrically equivalent to the completed
complex Hilbert tensor for arbitrary σ-finite factors. -/
def l2ProductCompletedTensorEquiv_sigmaFinite :
    UniformSpace.Completion (Lp ℂ 2 μ ⊗[ℂ] Lp ℂ 2 ν) ≃ₗᵢ[ℂ] Lp ℂ 2 (μ.prod ν) :=
  LinearIsometryEquiv.ofSurjective l2ProductCompletedTensorIsometry
    l2ProductCompletedTensorIsometry_surjective_sigmaFinite

end
end GinibrePoincare
