module
public import GinibrePoincare.Analysis.CorrespondenceGUEProjection
@[expose] public section
open MeasureTheory Set
open scoped ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem gueOrderedMeasure_square_lsi {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (hs : HasCompactSupport f) :
    squareEntropy (gueOrderedMeasure n) f ≤
      (2/(n:ℝ))*∫x,‖gradient f x‖^2 ∂gueOrderedMeasure n := by
  obtain ⟨M,hM⟩ := hf.continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support (hs.fderiv ℝ)
  let K : ℝ≥0 := ⟨max M 0,le_max_right _ _⟩
  have hLip : LipschitzWith K f := lipschitzWith_of_nnnorm_fderiv_le
    (hf.differentiable (by norm_num)) (fun x => by
      change ‖fderiv ℝ f x‖≤max M 0
      exact (hM x).trans (le_max_left _ _))
  obtain ⟨C,hC⟩ := hf.continuous.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hb (x) : ‖f x‖≤C := hC (mem_range_self x)
  have hL := gueDoubledOrderedMeasure_boundedC1_square_lsi hn
    (f ∘ gueRealProjection n) (hf.comp ((gueRealProjection_contDiff n).of_le (by norm_num)))
    (K*‖gueRealProjectionLinear n‖₊)
    (hLip.comp (gueRealProjectionLinear n).lipschitzWith) C (fun x => hb _)
  have he : squareEntropy (gueDoubledOrderedMeasure n) (f ∘ gueRealProjection n)=
      squareEntropy (gueOrderedMeasure n) f := by
    unfold squareEntropy
    simp only [Function.comp_apply]
    rw [gueOrderedMeasure_real_marginal_integral hn (fun x => f x^2*Real.log (f x^2)),
      gueOrderedMeasure_real_marginal_integral hn (fun x => f x^2)]
  rw [he] at hL
  simp_rw [gueRealProjection_gradient_norm_sq n f hf] at hL
  rw [gueOrderedMeasure_real_marginal_integral hn (fun x => ‖gradient f x‖^2)] at hL
  exact hL


theorem gueOrderedMeasure_boundedC1_square_lsi {n : ℕ} (hn : 0<n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (K : ℝ≥0) (hK : LipschitzWith K f) (C : ℝ) (hb : ∀x,‖f x‖≤C) :
    squareEntropy (gueOrderedMeasure n) f ≤
      (2/(n:ℝ))*∫x,‖gradient f x‖^2 ∂gueOrderedMeasure n := by
  have hL := gueDoubledOrderedMeasure_boundedC1_square_lsi hn
    (f ∘ gueRealProjection n) (hf.comp ((gueRealProjection_contDiff n).of_le (by norm_num)))
    (K*‖gueRealProjectionLinear n‖₊)
    (hK.comp (gueRealProjectionLinear n).lipschitzWith) C (fun x => hb _)
  have he : squareEntropy (gueDoubledOrderedMeasure n) (f ∘ gueRealProjection n)=
      squareEntropy (gueOrderedMeasure n) f := by
    unfold squareEntropy
    simp only [Function.comp_apply]
    rw [gueOrderedMeasure_real_marginal_integral hn (fun x => f x^2*Real.log (f x^2)),
      gueOrderedMeasure_real_marginal_integral hn (fun x => f x^2)]
  rw [he] at hL
  simp_rw [gueRealProjection_gradient_norm_sq n f hf] at hL
  rw [gueOrderedMeasure_real_marginal_integral hn (fun x => ‖gradient f x‖^2)] at hL
  exact hL

#print axioms gueOrderedMeasure_boundedC1_square_lsi

#print axioms gueOrderedMeasure_square_lsi
end
end GinibrePoincare
