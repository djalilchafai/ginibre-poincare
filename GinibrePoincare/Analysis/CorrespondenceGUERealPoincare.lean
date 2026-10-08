module
public import GinibrePoincare.Analysis.CorrespondenceGUERealLSI
public import GinibrePoincare.Analysis.SquareEntropyLinearization
@[expose] public section
open MeasureTheory Set
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

theorem gueOrderedMeasure_poincare_compactC1 {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) :
    (∫x,f x^2 ∂gueOrderedMeasure n)-(∫x,f x ∂gueOrderedMeasure n)^2 ≤
      (1/(n:ℝ))*∫x,‖gradient f x‖^2 ∂gueOrderedMeasure n := by
  letI := gueOrderedMeasure_probability hn
  obtain ⟨M,hM⟩ := hf.continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support (hs.fderiv ℝ)
  let K : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  have hLip : LipschitzWith K f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => by
      change ‖fderiv ℝ f x‖≤max M 0
      exact (hM x).trans (le_max_left _ _))
  obtain ⟨C,hC⟩ := hf.continuous.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hb (x) : ‖f x‖≤C := hC (mem_range_self x)
  have hlin := squareEntropy_affine_bound_variance (gueOrderedMeasure n) f hf.continuous.measurable
    C ((norm_nonneg (f 0)).trans (hb 0)) (by simpa only [Real.norm_eq_abs] using hb)
    ((2/(n:ℝ))*∫x,‖gradient f x‖^2 ∂gueOrderedMeasure n) (by
      intro t
      have hft : ContDiff ℝ 1 (fun x => 1+t*f x) := contDiff_const.add (contDiff_const.mul hf)
      have hdt (x) : fderiv ℝ (fun x => 1+t*f x) x = t • fderiv ℝ f x := by
        rw [fderiv_const_add,fderiv_const_mul (hf.differentiable (by norm_num) x)]
      have hLipT : LipschitzWith (‖t‖₊*K) (fun x => 1+t*f x) :=
        lipschitzWith_of_nnnorm_fderiv_le (hft.differentiable (by norm_num)) (fun x => by
          rw [hdt,nnnorm_smul]
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          change ‖fderiv ℝ f x‖≤max M 0
          exact (hM x).trans (le_max_left _ _))
      have hbT (x) : ‖1+t*f x‖≤1+|t| *C := by
        calc
          _ ≤ ‖(1:ℝ)‖+‖t*f x‖ := norm_add_le _ _
          _ = 1+|t| *‖f x‖ := by rw [norm_mul,Real.norm_eq_abs t]; norm_num
          _ ≤ 1+|t| *C := add_le_add_right (mul_le_mul_of_nonneg_left (hb x) (abs_nonneg t)) _
      have hL := gueOrderedMeasure_boundedC1_square_lsi hn _ hft _ hLipT _ hbT
      have hg (x) : gradient (fun x => 1+t*f x) x=t • gradient f x := by
        unfold gradient
        rw [fderiv_const_add,fderiv_const_mul (hf.differentiable (by norm_num) x)]
        simp only [map_smul]
      simp_rw [hg,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs] at hL
      rw [integral_const_mul] at hL
      convert hL using 1 <;> ring)
  convert hlin using 1 <;> ring

#print axioms gueOrderedMeasure_poincare_compactC1
end
end GinibrePoincare
