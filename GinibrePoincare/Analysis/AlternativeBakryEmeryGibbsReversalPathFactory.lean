module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinConfiguration
@[expose] public section
open Set MeasureTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance bakryGibbsFactory_configPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := borel _
local instance bakryGibbsFactory_configPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ),Configuration n) := ⟨rfl⟩
local instance bakryGibbsFactory_hilbertPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ),EuclideanSpace ℝ (Fin n × Fin 2)) := borel _
local instance bakryGibbsFactory_hilbertPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ),EuclideanSpace ℝ (Fin n × Fin 2)) := ⟨rfl⟩

/-- The actual globally defined measurable ordinary-gradient configuration
path selected from its literal continuous driver. -/
def bakryEmeryGibbsPath {n : ℕ} (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) (T : ℝ≥0)
    (p : Configuration n × C(Icc (0 : ℝ) (T : ℝ),EuclideanSpace ℝ (Fin n × Fin 2))) :
    C(Icc (0 : ℝ) (T : ℝ),Configuration n) :=
  let e := configurationEuclideanEquiv n
  let U := W ∘ e.symm
  let path := bakryEmeryLangevinPath U κ hκ (hW.comp e.symm.contDiff) hc T T.property (e p.1,p.2)
  ⟨fun t => e.symm (path t), e.symm.continuous.comp path.continuous⟩

theorem bakryEmeryGibbsPath_measurable {n : ℕ} (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) (T : ℝ≥0) :
    Measurable (bakryEmeryGibbsPath W hW κ hκ hc T) := by
  letI : Nonempty (Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0,⟨le_rfl,T.property⟩⟩⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  exact (configurationEuclideanEquiv n).symm.continuous.measurable.comp
    ((continuous_eval_const t).measurable.comp
      ((bakryEmeryLangevinPath_measurable (W ∘ (configurationEuclideanEquiv n).symm) κ hκ
        (hW.comp (configurationEuclideanEquiv n).symm.contDiff) hc T T.property).comp
          (((configurationEuclideanEquiv n).continuous.measurable.comp measurable_fst).prodMk measurable_snd)))

@[simp] theorem bakryEmeryGibbsPath_initial {n : ℕ} (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2)) (T : ℝ≥0)
    (p : Configuration n × C(Icc (0 : ℝ) (T : ℝ),EuclideanSpace ℝ (Fin n × Fin 2))) :
    bakryEmeryGibbsPath W hW κ hκ hc T p ⟨0,⟨le_rfl,T.property⟩⟩ =
      p.1+(configurationEuclideanEquiv n).symm (p.2 ⟨0,⟨le_rfl,T.property⟩⟩) := by
  unfold bakryEmeryGibbsPath
  simp only [ContinuousMap.coe_mk]
  rw [bakryEmeryLangevinPath_initial]
  simp only [map_add, ContinuousLinearEquiv.symm_apply_apply]

theorem bakryEmeryGibbsPath_prefix_identification {n : ℕ} (W : Configuration n → ℝ)
    (hW : ContDiff ℝ 2 W) (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (z : Configuration n) (T : ℝ≥0)
    (N : C(Icc (0 : ℝ) (T : ℝ),EuclideanSpace ℝ (Fin n × Fin 2)))
    (τ : ℝ) (hτ : 0 ≤ τ) (hτT : τ ≤ T) (X : ℝ → Configuration n)
    (hX : ContinuousOn X (Icc 0 τ))
    (hEq : ∀ t ∈ Icc 0 τ, X t = z+
      (configurationEuclideanEquiv n).symm (bkWeightedExtension T T.property N t)+
      ∫ s in (0 : ℝ)..t, bakryEmeryGibbsConfigurationDrift W (X s)) :
    ∀ t (ht : t ∈ Icc 0 τ), bakryEmeryGibbsPath W hW κ hκ hc T (z,N)
      ⟨t,⟨ht.1,ht.2.trans hτT⟩⟩ = X t := by
  have hId := bakryEmery_configuration_volterra_prefix_identification n W hW κ hκ hc z T T.property
    N τ hτ hτT X hX hEq
  intro t ht
  have he := congrArg (configurationEuclideanEquiv n).symm (hId t ht)
  exact (by simpa only [ContinuousLinearEquiv.symm_apply_apply, bakryEmeryGibbsPath,
    ContinuousMap.coe_mk, bakryEmeryLangevinPath] using he.symm)

#print axioms bakryEmeryGibbsPath_prefix_identification
#print axioms bakryEmeryGibbsPath_measurable
#print axioms bakryEmeryGibbsPath_initial
end
end GinibrePoincare
