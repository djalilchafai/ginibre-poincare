module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryJointMollification
public import GinibrePoincare.Analysis.NonQuadraticWeyl
public import Mathlib.MeasureTheory.Integral.Pi

@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def configurationRadialSmoothingKernel (n : ℕ) (z : Configuration n) : ℝ :=
  ∏ i, planarRadialSmoothingKernel (z i)

theorem configurationRadialSmoothingKernel_contDiff (n : ℕ) :
    ContDiff ℝ ∞ (configurationRadialSmoothingKernel n) := by
  exact contDiff_prod (fun i _ => planarRadialSmoothingKernel_contDiff.comp (contDiff_apply ℝ ℂ i))

theorem configurationRadialSmoothingKernel_compact (n : ℕ) :
    HasCompactSupport (configurationRadialSmoothingKernel n) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Configuration n) 2)
  intro z hz
  rw [Metric.mem_closedBall,dist_zero_right]
  apply pi_norm_le_iff_of_nonneg (by norm_num) |>.mpr
  intro i
  have hzi : planarRadialSmoothingKernel (z i) ≠ 0 := by
    intro hi
    exact hz (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have hbase : planarRadialSmoothingBase (z i) ≠ 0 := by
    intro h
    exact hzi (by simp [planarRadialSmoothingKernel,h])
  have hpos : 0 < 2-Complex.normSq (z i) := by
    by_contra h
    exact hbase (Real.smoothTransition.zero_of_nonpos (le_of_not_gt h))
  rw [Complex.normSq_eq_norm_sq] at hpos
  nlinarith [norm_nonneg (z i)]

theorem configurationRadialSmoothingKernel_integral (n : ℕ) :
    (∫ z : Configuration n, configurationRadialSmoothingKernel n z) = 1 := by
  unfold configurationRadialSmoothingKernel
  rw [integral_fin_nat_prod_volume_eq_prod]
  simp only [planarRadialSmoothingKernel_integral,Finset.prod_const_one]

/-- Tensor radial smoothing reproduces every genuine jointly entire
function, without an integrability assumption at infinity. -/
theorem configurationRadialSmoothing_mean_value (n : ℕ)
    (F : Configuration n → ℂ) (hF : Differentiable ℂ F) (x : Configuration n) :
    (∫ y : Configuration n, configurationRadialSmoothingKernel n y • F (x-y)) = F x := by
  induction n with
  | zero =>
    have hc : ∀ y : Configuration 0, F (x-y) = F x :=
      fun y => congrArg F (Subsingleton.elim _ _)
    simp_rw [hc]
    rw [integral_smul_const,configurationRadialSmoothingKernel_integral,one_smul]
  | succ n ih =>
    let H : Configuration (n+1) → ℂ := fun y =>
      configurationRadialSmoothingKernel (n+1) y • F (x-y)
    have hH : Integrable H volume :=
      ((configurationRadialSmoothingKernel_contDiff (n+1)).continuous.smul
        (hF.continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          ((configurationRadialSmoothingKernel_compact (n+1)).smul_right)
    have he := (volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm
    have hcons (a : ℂ × Configuration n) :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm a =
        Fin.cons a.1 a.2 := by
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hc : Continuous (fun a : ℂ × Configuration n => (Fin.cons a.1 a.2 : Configuration (n+1))) := by
      fun_prop
    have hcomp : Integrable (fun a : ℂ × Configuration n => H (Fin.cons a.1 a.2)) volume := by
      have hh := (he.integrable_comp hH.aestronglyMeasurable).mpr hH
      simpa only [Function.comp_def,hcons] using hh
    rw [← he.integral_comp' H]
    simp only [hcons]
    change (∫ a : ℂ × Configuration n, H (Fin.cons a.1 a.2) ∂
      (volume : Measure ℂ).prod (volume : Measure (Configuration n))) = F x
    have hcomp' : Integrable (fun a : ℂ × Configuration n => H (Fin.cons a.1 a.2))
      ((volume : Measure ℂ).prod (volume : Measure (Configuration n))) := hcomp
    rw [integral_prod_symm _ hcomp']
    have hinner (y : Configuration n) :
        (∫ a : ℂ, H (Fin.cons a y)) =
          configurationRadialSmoothingKernel n y • F (Fin.cons (x 0) (Fin.tail x-y)) := by
      have hd : Differentiable ℂ (fun a : ℂ => F (Fin.cons a (Fin.tail x-y))) := by
        apply hF.comp
        fun_prop
      have hmv := radial_integral_holomorphic_mean_value planarRadialSmoothingKernel
        planarRadialSmoothingKernel_contDiff.continuous planarRadialSmoothingKernel_compact
        planarRadialSmoothingKernel_radial (fun a => F (Fin.cons a (Fin.tail x-y))) hd (x 0)
      rw [planarRadialSmoothingKernel_integral,one_smul] at hmv
      have hfunc : (fun a : ℂ => H (Fin.cons a y)) =
          (fun a : ℂ => configurationRadialSmoothingKernel n y •
            (planarRadialSmoothingKernel a • F (Fin.cons (x 0-a) (Fin.tail x-y)))) := by
        funext a
        unfold H configurationRadialSmoothingKernel
        rw [Fin.prod_univ_succ]
        simp only [Fin.cons_zero,Fin.cons_succ]
        have hsub : x-Fin.cons a y = Fin.cons (x 0-a) (Fin.tail x-y) := by
          funext i
          refine Fin.cases ?_ (fun j => ?_) i <;> simp [Fin.tail]
        rw [hsub]
        simp only [smul_smul]
        congr 1
        ring
      rw [hfunc,integral_smul,hmv]
    simp_rw [hinner]
    have hd : Differentiable ℂ (fun y : Configuration n => F (Fin.cons (x 0) y)) := by
      apply hF.comp
      fun_prop
    have hh := ih (fun y => F (Fin.cons (x 0) y)) hd (Fin.tail x)
    simpa only [Fin.cons_self_tail] using hh

#print axioms configurationRadialSmoothing_mean_value
#print axioms configurationRadialSmoothingKernel_contDiff
#print axioms configurationRadialSmoothingKernel_compact
#print axioms configurationRadialSmoothingKernel_integral
end
end GinibrePoincare
