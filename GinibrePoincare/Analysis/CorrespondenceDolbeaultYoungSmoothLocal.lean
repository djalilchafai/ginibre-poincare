module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungSmooth

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dolbeaultCoordinateConvolution_truncation_local {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (f : Configuration n → ℂ) (M T R : ℝ) (hR : M+T≤R)
    (hM : ∀ w∈Function.support f, ‖w‖≤M) (x : Configuration n) (hx : ‖x‖≤T) :
    dolbeaultCoordinateConvolutionPointwise j ((Metric.closedBall 0 R).indicator k) f x =
      dolbeaultCoordinateConvolutionPointwise j k f x := by
  unfold dolbeaultCoordinateConvolutionPointwise
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    by_cases hy : y∈Metric.closedBall (0 : ℂ) R
    · rw [Set.indicator_of_mem hy]
    · have hz : f (x-Pi.single j y)=0 := by
        by_contra h
        have hb := hM _ h
        have he : y=x j-(x-Pi.single j y : Configuration n) j := by simp
        have hn : ‖y‖≤‖x‖+‖x-Pi.single j y‖ := by
          calc
            _ = ‖x j-(x-Pi.single j y : Configuration n) j‖ := congrArg norm he
            _ ≤ ‖x j‖+‖(x-Pi.single j y : Configuration n) j‖ := norm_sub_le _ _
            _ ≤ _ := add_le_add (norm_le_pi_norm _ j) (norm_le_pi_norm _ j)
        apply hy
        simp only [Metric.mem_closedBall, dist_zero_right]
        linarith
      rw [hz]
      simp)

/-- The literal smooth localized solver is the genuine coordinate kernel convolution. -/
theorem dolbeaultCoordinateConvolution_configurationPotential {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (f : Configuration n → ℂ) (x : Configuration n) :
    configurationCauchyGreenPotential j χ f x =
      dolbeaultCoordinateConvolutionPointwise j cauchyGreenKernel
        (fun z => χ (z j)*f z) x := by
  unfold configurationCauchyGreenPotential localizedCauchyGreenPotential
    parametricCauchyGreenPotential cauchyGreenPotential dolbeaultCoordinateConvolutionPointwise
  unfold MeasureTheory.convolution
  congr 1
  funext y
  have he : dolbeaultReplaceCoordinate j (x, x j-y)=x-Pi.single j y := by
    ext l
    by_cases hl : l=j
    · subst l
      simp [dolbeaultReplaceCoordinate_apply]
    · simp [dolbeaultReplaceCoordinate_apply, hl]
  simp only [he, Pi.sub_apply, Pi.single_eq_same]
  rfl

#print axioms dolbeaultCoordinateConvolution_configurationPotential
#print axioms dolbeaultCoordinateConvolution_truncation_local
end
end GinibrePoincare
