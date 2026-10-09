module

public import GinibrePoincare.Analysis.GinibreStochasticCompactStoppedSelection
public import GinibrePoincare.Analysis.FiniteDimensionalItoCoefficientBounds

@[expose] public section

/-! Actual local C² gradient and Hessian coefficients of compact adapted configuration paths. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem ginibreCompactProcess_scalar_stronglyAdapted {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → Configuration n) (hX : StronglyAdapted F X)
    (K : Set (Configuration n)) (hRange : ∀ t ω, X t ω ∈ K)
    (g : Configuration n → ℝ) (hg : ContinuousOn g K) :
    StronglyAdapted F (fun t ω => g (X t ω)) := by
  intro t
  have hm : @Measurable Ω K (F t) _ (fun ω => ⟨X t ω, hRange t ω⟩) := (hX t).measurable.subtype_mk
  exact hg.restrict.comp_stronglyMeasurable hm.stronglyMeasurable

theorem ginibreCompactProcess_test_coefficients {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (F : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (X : ℝ≥0 → Ω → Configuration n) (hX : StronglyAdapted F X)
    (hCont : ∀ ω, Continuous (fun t => X t ω))
    (f : Configuration n → ℝ) (U K : Set (Configuration n))
    (hU : IsOpen U) (hf : ContDiffOn ℝ 2 f U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hRange : ∀ t ω, X t ω ∈ K) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ i : Fin n × Fin 2,
        StronglyAdapted F (fun t ω => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)) ∧
        (∀ ω, Continuous (fun t => fderiv ℝ f (X t ω) (ginibreCoordinateDirection i))) ∧
        ∀ t ω, ‖fderiv ℝ f (X t ω) (ginibreCoordinateDirection i)‖ ≤ C) ∧
      ∀ i j : Fin n × Fin 2,
        StronglyAdapted F (fun t ω => itoConfigurationHessianEntry f (X t ω) i j) ∧
        (∀ ω, Continuous (fun t => itoConfigurationHessianEntry f (X t ω) i j)) ∧
        ∀ t ω, ‖itoConfigurationHessianEntry f (X t ω) i j‖ ≤ C := by
  obtain ⟨C, hC, hBound⟩ := itoConfigurationCoefficients_exists_bound f U K hU hf hK hKU
  refine ⟨C, hC,?_,?_⟩
  · intro i
    have hg := itoConfigurationGradientEntry_continuousOn f U hU hf i
    exact ⟨ginibreCompactProcess_scalar_stronglyAdapted n F X hX K hRange _ (hg.mono hKU),
      fun ω => hg.comp_continuous (hCont ω) (fun t => hKU (hRange t ω)),
      fun t ω => (hBound _ (hRange t ω)).1 i⟩
  · intro i j
    have hg := itoConfigurationHessianEntry_continuousOn f U hU hf i j
    exact ⟨ginibreCompactProcess_scalar_stronglyAdapted n F X hX K hRange _ (hg.mono hKU),
      fun ω => hg.comp_continuous (hCont ω) (fun t => hKU (hRange t ω)),
      fun t ω => (hBound _ (hRange t ω)).2 i j⟩

end
end GinibrePoincare
