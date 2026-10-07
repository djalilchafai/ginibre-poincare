module

public import GinibrePoincare.Analysis.BrownianOrthogonalPiGaussianLaw
public import GinibrePoincare.Analysis.GinibreStochasticBrownianFamilyPast

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- An orthogonal rotation selected from any finite block of the genuine joint
Brownian past preserves the fresh full Gaussian increment and its independence. -/
theorem brownianFamily_past_orthogonal_fresh_increment {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι] (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) [IsProbabilityMeasure P] (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (s t : ℝ≥0)
    (m : ℕ) (τ : Fin m → ℝ≥0) (hτ : ∀ j, τ j ≤ s)
    (U : (ι × Fin m → ℝ) → EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι)
    (hU : Measurable (fun p : (ι × Fin m → ℝ) × EuclideanSpace ℝ ι => U p.1 p.2)) :
    let Y := fun ω (q : ι × Fin m) => B q.1 (τ q.2) ω
    let X := fun ω => WithLp.toLp 2 (fun i => B i (s+t) ω - B i s ω)
    HasLaw (fun ω => U (Y ω) (X ω)) (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P ∧
      IndepFun Y (fun ω => U (Y ω) (X ω)) P := by
  classical
  dsimp only
  let Y := fun ω (q : ι × Fin m) => B q.1 (τ q.2) ω
  let X := fun ω => WithLp.toLp 2 (fun i => B i (s+t) ω - B i s ω)
  have hy : AEMeasurable Y P := AEMeasurable.of_eval
    (fun q => (hB q.1).aemeasurable (τ q.2))
  let ν := P.map Y
  letI : IsProbabilityMeasure ν := (by infer_instance)
  have hyl : HasLaw Y ν P := ⟨hy, rfl⟩
  have hxl : HasLaw X (scaledStandardGaussian (EuclideanSpace ℝ ι) t) P := by
    exact (show HasLaw (WithLp.toLp 2)
      (scaledStandardGaussian (EuclideanSpace ℝ ι) t)
      (Measure.pi (fun _ : ι => gaussianReal 0 t)) from
        ⟨by fun_prop, piGaussianReal_map_toLp_scaledStandard ι t⟩).fun_comp
      (ginibreBrownian_family_increment_hasLaw B P hB hind s t)
  have hi : IndepFun Y X P := by
    have hp := (ginibreBrownian_family_increment_independent_past B P hB hind s t).symm
    exact hp.comp
      (show Measurable (fun p : (ι × Set.Iic s → ℝ) =>
        fun q : ι × Fin m => p (q.1, ⟨τ q.2, hτ q.2⟩)) by fun_prop)
      (show Measurable (WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι) by fun_prop)
  exact independent_past_orthogonal_gaussian_transform (EuclideanSpace ℝ ι) P ν t Y X hyl hxl hi U hU

end
end GinibrePoincare
