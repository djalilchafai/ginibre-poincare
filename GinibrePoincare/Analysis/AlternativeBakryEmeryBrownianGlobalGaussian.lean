module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalPath
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
@[expose] public section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
local instance : MeasurableSpace C(Icc (0:ℝ) 1,ℝ) := borel _
local instance : BorelSpace C(Icc (0:ℝ) 1,ℝ) := ⟨rfl⟩
theorem bakryBrownianDyadicCompletedPath_isGaussian_of_original
    (hU : IsGaussianProcess (fun t : Icc (0:ℝ) 1 =>
      fun ω => bakryBrownianDyadicPath ω t) bakryBrownianDyadicMeasure) :
    IsGaussianProcess (fun t : Icc (0:ℝ) 1 =>
      fun ω => bakryBrownianDyadicCompletedPath ω t) bakryBrownianDyadicCompletedMeasure := by
  constructor
  intro I
  refine ⟨?_,?_⟩
  · apply Measurable.aemeasurable
    apply Measurable.of_eval
    intro i
    exact (continuous_eval_const i.val).measurable.comp bakryBrownianDyadicCompletedPath_measurable
  · change IsGaussian (bakryBrownianDyadicCompletedMeasure.map
      (fun ω : BakryBrownianDyadicCompletedSample => I.restrict (fun t => bakryBrownianDyadicPath ω t)))
    rw [bakryBrownianDyadic_completed_map _ (hU.hasGaussianLaw I).aemeasurable]
    exact (hU.hasGaussianLaw I).isGaussian_map

#print axioms bakryBrownianDyadicCompletedPath_isGaussian_of_original

theorem bakryBrownianGlobalProcess_isGaussian_of_unit
    (hU : IsGaussianProcess (fun t : Icc (0:ℝ) 1 =>
      fun ω => bakryBrownianDyadicCompletedPath ω t) bakryBrownianDyadicCompletedMeasure) :
    IsGaussianProcess bakryBrownianGlobalProcess bakryBrownianGlobalMeasure := by
  classical
  constructor
  intro I
  obtain ⟨N,hN⟩ := exists_nat_gt (∑ i : I, (i.val:ℝ))
  have htime (i : I) : (i.val:ℝ) ≤ N :=
    (Finset.single_le_sum (fun j _ => j.val.coe_nonneg) (Finset.mem_univ i)).trans hN.le
  let F : ℕ → BakryBrownianDyadicCompletedSample → (I → ℝ) :=
    fun n ω i => bakryBrownianDyadicCompletedPath ω (bakryBrownianUnitClamp ((i.val:ℝ)-n))
  have hF (n : ℕ) : Measurable (F n) := by
    apply Measurable.of_eval
    intro i
    exact (continuous_eval_const _).measurable.comp bakryBrownianDyadicCompletedPath_measurable
  have hFG (n : ℕ) : HasGaussianLaw (F n) bakryBrownianDyadicCompletedMeasure := by
    let ts : I → Icc (0:ℝ) 1 := fun i => bakryBrownianUnitClamp ((i.val:ℝ)-n)
    let K : ((Finset.univ.image ts) → ℝ) →L[ℝ] (I → ℝ) :=
      ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨ts i,by simp⟩)
    convert (hU.hasGaussianLaw (Finset.univ.image ts)).map K using 1
    funext ω i
    rfl
  have hG (n : Fin N) : HasGaussianLaw (fun ω : BakryBrownianGlobalSample => F n (ω n))
      bakryBrownianGlobalMeasure := by
    have hp := measurePreserving_eval_infinitePi (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure) n.val
    refine ⟨((hF n).comp hp.measurable).aemeasurable,?_⟩
    change IsGaussian (bakryBrownianGlobalMeasure.map ((F n) ∘ (fun ω => ω n)))
    rw [←Measure.map_map (hF n) hp.measurable]
    change IsGaussian ((Measure.infinitePi (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure)).map (fun ω => ω n) |>.map (F n))
    rw [hp.map_eq]
    exact (hFG n).isGaussian_map
  have hi : iIndepFun (fun n : Fin N => fun ω : BakryBrownianGlobalSample => F n (ω n))
      bakryBrownianGlobalMeasure := by
    exact (iIndepFun_infinitePi hF).precomp Fin.val_injective
  have hg := hi.hasGaussianLaw_fun_sum hG
  convert hg using 1
  funext ω i
  simp only [Finset.sum_apply,Finset.restrict_def,bakryBrownianGlobalProcess]
  change bakryBrownianGlobalPath ω i.val = ∑ n : Fin N, F n (ω n) i
  rw [bakryBrownianGlobalPath_eq_finite ω N i.val (htime i)]
  exact (Fin.sum_univ_eq_sum_range (fun n => F n (ω n) i) N).symm

#print axioms bakryBrownianGlobalProcess_isGaussian_of_unit
end
end GinibrePoincare
