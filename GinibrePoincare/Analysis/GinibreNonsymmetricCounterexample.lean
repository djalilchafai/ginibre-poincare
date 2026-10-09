module

public import GinibrePoincare.Analysis.GinibreNonsymmetricCounterexampleCoordinates

@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

def ginibreRealParticleCoordinateCLM {n : ℕ} (i : Fin n) : Configuration n →L[ℝ] ℝ :=
  Complex.reCLM.comp (ContinuousLinearMap.proj i)

theorem ginibre_coordinate_re_integrable (n : ℕ) (hn : 2≤n) (i : Fin n) :
    Integrable (fun z : Configuration n => (z i).re) (ginibreMeasure n) := by
  letI := ginibreMeasure_isProbabilityMeasure (by omega : 0<n)
  have h : MemLp (fun z : Configuration n => (z i).re) 2 (ginibreMeasure n) := by
    apply (memLp_two_iff_integrable_sq_norm
      (show Continuous (fun z : Configuration n => (z i).re) by fun_prop).aestronglyMeasurable).mpr
    simpa [Real.norm_eq_abs] using ginibre_coordinate_re_sq_integrable n hn i
  exact h.integrable (by norm_num)

theorem ginibre_coordinate_re_mean_zero (n : ℕ) (hn : 2≤n) (i : Fin n) :
    (∫ z : Configuration n, (z i).re ∂ginibreMeasure n)=0 := by
  have hp := measurePreserving_globalPhase_ginibreMeasure (by omega : 0<n)
    (-1 : ℂ) (by simp)
  have h := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re)
      ((ginibreMeasure n).map (globalPhase (-1 : ℂ))) from
      (show Continuous (fun z : Configuration n => (z i).re) by fun_prop).aestronglyMeasurable)
  rw [hp.map_eq] at h
  simp only [globalPhase, neg_one_mul, Complex.neg_re, integral_neg] at h
  linarith

theorem ginibre_coordinate_re_gradient_normSq (n : ℕ) (i : Fin n) (z : Configuration n) :
    realGradientNormSq (fun w : Configuration n => (w i).re) z=1 := by
  have he : (fun w : Configuration n => (w i).re)=ginibreRealParticleCoordinateCLM i := rfl
  unfold realGradientNormSq
  rw [he]
  simp only [ContinuousLinearMap.fderiv, ginibreRealParticleCoordinateCLM,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.reCLM_apply,
    realCoordinateDirection, imaginaryCoordinateDirection, coordinateDirection]
  have hterm (k : Fin n) :
      (if i=k then (1 : ℂ) else 0).re^2+(if i=k then Complex.I else 0).re^2=
      if k=i then (1 : ℝ) else 0 := by
    by_cases h : k=i
    · subst k; simp
    · simp [h, Ne.symm h]
  simp_rw [hterm]
  simp

theorem ginibre_coordinate_re_variance (n : ℕ) (hn : 2≤n) (i : Fin n) :
    smoothGinibreVariance n (fun z : Configuration n => (z i).re)=((n : ℝ)+1)/(4*(n : ℝ)) := by
  unfold smoothGinibreVariance smoothGinibreMean
  rw [ginibre_coordinate_re_mean_zero n hn i]
  simpa using ginibre_coordinate_re_sq_integral n hn i

theorem ginibre_coordinate_re_energy (n : ℕ) (hn : 2≤n) (i : Fin n) :
    smoothGinibreEnergy n (fun z : Configuration n => (z i).re)=1/(n : ℝ) := by
  letI := ginibreMeasure_isProbabilityMeasure (by omega : 0<n)
  unfold smoothGinibreEnergy
  simp_rw [ginibre_coordinate_re_gradient_normSq]
  simp

theorem ginibre_coordinate_re_not_symmetric (n : ℕ) (hn : 2≤n) (i : Fin n) :
    ¬IsSymmetric (fun z : Configuration n => (z i).re) := by
  letI : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  obtain ⟨j, hji⟩ := exists_ne i
  intro h
  have he := h (Equiv.swap i j) (fun k => if k=i then (1 : ℂ) else 0)
  simp [permute, hji] at he

theorem ginibre_coordinate_re_gradient_integrable (n : ℕ) (hn : 2≤n) (i : Fin n) :
    Integrable (realGradientNormSq (fun z : Configuration n => (z i).re)) (ginibreMeasure n) := by
  letI := ginibreMeasure_isProbabilityMeasure (by omega : 0<n)
  have he : realGradientNormSq (fun z : Configuration n => (z i).re)=(fun _ => (1 : ℝ)) :=
    funext (ginibre_coordinate_re_gradient_normSq n i)
  rw [he]
  exact integrable_const 1

theorem ginibre_nonsymmetric_poincare_constant_lower_bound (n : ℕ) (hn : 2≤n)
    (C : ℝ) (hC : ∀ f : Configuration n → ℝ, ContDiff ℝ ⊤ f →
      Integrable f (ginibreMeasure n) → Integrable (fun z => f z^2) (ginibreMeasure n) →
      Integrable (realGradientNormSq f) (ginibreMeasure n) →
      smoothGinibreVariance n f≤C*smoothGinibreEnergy n f) : ((n : ℝ)+1)/4≤C := by
  let i : Fin n := ⟨0, by omega⟩
  have h := hC (fun z => (z i).re)
    (ginibreRealParticleCoordinateCLM i).contDiff
    (ginibre_coordinate_re_integrable n hn i) (ginibre_coordinate_re_sq_integrable n hn i)
    (ginibre_coordinate_re_gradient_integrable n hn i)
  rw [ginibre_coordinate_re_variance n hn i, ginibre_coordinate_re_energy n hn i] at h
  have hnR : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  have hmul := (mul_le_mul_iff_of_pos_right hnR).mpr h
  field_simp at hmul
  linarith

#print axioms ginibre_nonsymmetric_poincare_constant_lower_bound
end
end GinibrePoincare
