module

public import GinibrePoincare.Analysis.GinibreNonsymmetricCounterexampleMoments
public import GinibrePoincare.Analysis.GinibreWeakPermutation

@[expose] public section
open MeasureTheory Set
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

theorem ginibre_coordinate_re_sq_integrable (n : ℕ) (hn : 2≤n) (i : Fin n) :
    Integrable (fun z : Configuration n => (z i).re^2) (ginibreMeasure n) := by
  apply (ginibre_configurationNormSq_integrable n hn).mono'
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re^2) (ginibreMeasure n) from (show Continuous (fun z : Configuration n => (z i).re^2) by fun_prop).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  have h := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  simp only [Real.norm_eq_abs, abs_sq]
  change (z i).re^2≤∑ j, Complex.normSq (z j)
  have hi : (z i).re^2≤Complex.normSq (z i) := by rw [Complex.normSq_apply]; nlinarith [sq_nonneg (z i).im]
  exact hi.trans h

theorem ginibre_coordinate_im_sq_integrable (n : ℕ) (hn : 2≤n) (i : Fin n) :
    Integrable (fun z : Configuration n => (z i).im^2) (ginibreMeasure n) := by
  apply (ginibre_configurationNormSq_integrable n hn).mono'
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).im^2) (ginibreMeasure n) from (show Continuous (fun z : Configuration n => (z i).im^2) by fun_prop).aestronglyMeasurable)
  apply Filter.Eventually.of_forall
  intro z
  have h := Finset.single_le_sum (fun j _ => Complex.normSq_nonneg (z j)) (Finset.mem_univ i)
  simp only [Real.norm_eq_abs, abs_sq]
  change (z i).im^2≤∑ j, Complex.normSq (z j)
  have hi : (z i).im^2≤Complex.normSq (z i) := by rw [Complex.normSq_apply]; nlinarith [sq_nonneg (z i).re]
  exact hi.trans h

theorem ginibre_coordinate_re_sq_eq_im_sq (n : ℕ) (hn : 2≤n) (i : Fin n) :
    (∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n)=
      ∫ z : Configuration n, (z i).im^2 ∂ginibreMeasure n := by
  have hp := measurePreserving_globalPhase_ginibreMeasure (by omega : 0<n)
    Complex.I (by simp)
  have h := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re^2)
      ((ginibreMeasure n).map (globalPhase Complex.I)) from
      (show Continuous (fun z : Configuration n => (z i).re^2) by fun_prop).aestronglyMeasurable)
  rw [hp.map_eq] at h
  simpa [globalPhase, Complex.mul_re] using h

theorem ginibre_coordinate_re_sq_eq (n : ℕ) (hn : 2≤n) (i j : Fin n) :
    (∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n)=
      ∫ z : Configuration n, (z j).re^2 ∂ginibreMeasure n := by
  have hp := ginibre_measurePreserving_permute (Equiv.swap i j)
  have h := integral_map hp.measurable.aemeasurable
    (show AEStronglyMeasurable (fun z : Configuration n => (z i).re^2)
      ((ginibreMeasure n).map (permute (Equiv.swap i j))) from
      (show Continuous (fun z : Configuration n => (z i).re^2) by fun_prop).aestronglyMeasurable)
  rw [hp.map_eq] at h
  simpa [permute] using h

theorem ginibre_coordinate_re_sq_integral (n : ℕ) (hn : 2≤n) (i : Fin n) :
    (∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n)=((n : ℝ)+1)/(4*(n : ℝ)) := by
  have hsum : (∫ z, configurationNormSq z ∂ginibreMeasure n)=
      2*(n : ℝ)*(∫ z : Configuration n, (z i).re^2 ∂ginibreMeasure n) := by
    unfold configurationNormSq
    simp_rw [Complex.normSq_apply,← sq]
    rw [integral_finsetSum _ (fun j _ =>
      show Integrable (fun z : Configuration n => (z j).re^2+(z j).im^2) (ginibreMeasure n) from
      (ginibre_coordinate_re_sq_integrable n hn j).add (ginibre_coordinate_im_sq_integrable n hn j))]
    simp_rw [integral_add (ginibre_coordinate_re_sq_integrable n hn _)
      (ginibre_coordinate_im_sq_integrable n hn _),← ginibre_coordinate_re_sq_eq_im_sq n hn]
    simp_rw [ginibre_coordinate_re_sq_eq n hn _ i]
    simp
    ring
  rw [ginibre_configurationNormSq_integral n hn] at hsum
  have hnR : 0<(n : ℝ) := by exact_mod_cast (show 0<n by omega)
  apply (eq_div_iff (by positivity : 4*(n : ℝ)≠0)).mpr
  linarith

#print axioms ginibre_coordinate_re_sq_integral
end
end GinibrePoincare
