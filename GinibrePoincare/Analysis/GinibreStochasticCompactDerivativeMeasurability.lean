module

public import GinibrePoincare.Analysis.GinibreStochasticCompactTaylorMeasurability

@[expose] public section

/-! Measurability of actual local test derivatives evaluated on measurable increments. -/
open Set MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

theorem ginibreCompact_fderiv_apply_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X H : Ω → Configuration n) (hmX : Measurable X) (hmH : Measurable H)
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hKU : K ⊆ U)
    (hRange : ∀ ω, X ω ∈ K) : Measurable (fun ω => fderiv ℝ f (X ω) (H ω)) := by
  have hdf : Measurable (fun ω => fderiv ℝ f (X ω)) :=
    ((hf.continuousOn_fderiv_of_isOpen hU (by norm_num)).mono hKU).restrict.measurable.comp
      (hmX.subtype_mk : Measurable (fun ω => (⟨X ω, hRange ω⟩ : K)))
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp (hdf.prodMk hmH)

theorem ginibreCompact_hessian_apply_measurable {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (X H : Ω → Configuration n) (hmX : Measurable X) (hmH : Measurable H)
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hKU : K ⊆ U)
    (hRange : ∀ ω, X ω ∈ K) : Measurable (fun ω => itoDirectionalHessian f (X ω) (H ω)) := by
  classical
  have hc (i : Fin n × Fin 2) : Measurable (fun ω => configurationEuclideanLinearEquiv n (H ω) i) :=
    ((configurationEuclideanLinearEquiv n).toContinuousLinearEquiv.continuous.measurable.comp hmH).eval
  have hh (i j : Fin n × Fin 2) : Measurable (fun ω => itoConfigurationHessianEntry f (X ω) i j) :=
    ((itoConfigurationHessianEntry_continuousOn f U hU hf i j).mono hKU).restrict.measurable.comp
      (hmX.subtype_mk : Measurable (fun ω => (⟨X ω, hRange ω⟩ : K)))
  simp_rw [itoConfigurationHessian_coordinate_sum]
  exact Finset.measurable_sum Finset.univ (fun i hi => Finset.measurable_sum Finset.univ
    (fun j hj => ((hc i).mul (hc j)).mul (hh i j)))
end
end GinibrePoincare
