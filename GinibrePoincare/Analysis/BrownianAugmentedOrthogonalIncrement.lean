module

public import GinibrePoincare.Analysis.BrownianAugmentedFreshIncrement
public import GinibrePoincare.Analysis.BrownianOrthogonalFreshIncrement

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem brownianFamily_augmented_orthogonal_fresh_increment {Ω ι A : Type*}
    [mAmbient : MeasurableSpace Ω] [Fintype ι] [MeasurableSpace A]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0) (Y : Ω → A)
    (hY : @Measurable Ω A (ginibreBrownianAugmentedFiltration B P hB s) _ Y)
    (U : A → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : A × EuclideanSpace ℝ ι => U p.1 p.2)) :
    let X := fun ω => WithLp.toLp 2 (fun i => B i (s+t) ω-B i s ω)
    HasLaw (fun ω => U (Y ω) (X ω)) (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P ∧
      IndepFun Y (fun ω => U (Y ω) (X ω)) P := by
  dsimp only
  let X := fun ω => WithLp.toLp 2 (fun i => B i (s+t) ω-B i s ω)
  have hy : @Measurable Ω A mAmbient _ Y := hY.mono
    ((ginibreBrownianAugmentedFiltration B P hB).le' s) le_rfl
  let ν := P.map Y
  letI : IsProbabilityMeasure ν := (by infer_instance)
  have hyl : HasLaw Y ν P := ⟨hy.aemeasurable, rfl⟩
  have hxl : HasLaw X (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P :=
    (show HasLaw (WithLp.toLp 2) (scaledStandardGaussian (EuclideanSpace ℝ ι) t)
      (Measure.pi (fun _ : ι => gaussianReal 0 t)) from
      ⟨by fun_prop, piGaussianReal_map_toLp_scaledStandard ι t⟩).fun_comp
        (ginibreBrownian_family_increment_hasLaw B P hB hind s t)
  have hi : IndepFun Y X P := by
    have hh := brownianFamily_fresh_increment_independent_augmented_variable B P hB hind s t Y hY
    exact (hh.comp (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)
      measurable_id).symm
  exact independent_past_orthogonal_gaussian_transform (EuclideanSpace ℝ ι) P ν t Y X hyl hxl hi U hU

end
end GinibrePoincare
