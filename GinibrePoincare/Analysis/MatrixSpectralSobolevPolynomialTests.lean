module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevPolynomialWeak
public import GinibrePoincare.Analysis.MatrixSpectralSobolevWeakMultiplier

@[expose] public section

/-! # Full compact-test identities without any collision boundary term -/
open MeasureTheory Filter MvPolynomial
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem polynomial_collision_real_first_weak_test (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : Configuration (d + 1) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z)
    (hf : LocallyIntegrable F volume)
    (hg : LocallyIntegrable (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) volume)
    (θ : Configuration (d + 1) → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) :
    (∫ z, fderiv ℝ F z (Fin.cons (1 : ℂ) 0) * θ z) =
      -(∫ z, F z * fderiv ℝ θ z (Fin.cons (1 : ℂ) 0)) := by
  let T := configurationRealFirstSplit d
  let ψ := θ ∘ T
  have hψ : ContDiff ℝ ∞ ψ := hθ.comp T.contDiff
  have hψc : HasCompactSupport ψ := hc.comp_homeomorph T.toHomeomorph
  obtain ⟨C, hC⟩ := hψc.exists_bound_of_continuousOn
    (continuous_fst : Continuous (fun q : ℝ × (ℝ × Configuration d) => q.1)).continuousOn
  have hsupp (y : ℝ × Configuration d) :
      tsupport (fun t => ψ (t, y)) ⊆ Set.Ioo (-|C| - 1) (|C| + 1) := by
    intro t ht
    have ht' : (t, y) ∈ tsupport ψ :=
      tsupport_comp_subset_preimage ψ
        (show Continuous (fun t : ℝ => (t, y)) from by fun_prop) ht
    have hb : |t| ≤ C := by simpa using hC (t, y) ht'
    have hab : |t| ≤ |C| := hb.trans (le_abs_self C)
    constructor <;> linarith [neg_abs_le t, le_abs_self t]
  have hgi := local_integrable_mul_compact_test (d + 1)
    (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) θ hg hθ.continuous hc
  have hfi := local_integrable_mul_compact_test (d + 1) F
    (fun z => fderiv ℝ θ z (Fin.cons (1 : ℂ) 0)) hf
    ((hθ.continuous_fderiv (by simp)).clm_apply continuous_const)
    (hc.fderiv_apply ℝ _)
  have hMP := configurationRealFirstSplit_volume_preserving d
  have hline (t : ℝ) (y : ℝ × Configuration d) :
      deriv (fun s => ψ (s, y)) t =
        fderiv ℝ θ (T (t, y)) (Fin.cons (1 : ℂ) 0) :=
    ((hθ.differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t
      (configurationRealFirstSplit_line_hasDerivAt d y t)).deriv
  have h := product_weak_derivative_identity_of_finite_crossings
    (volume : Measure (ℝ × Configuration d))
    (F ∘ T) ((fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) ∘ T)
    ψ ((fun z => fderiv ℝ θ z (Fin.cons (1 : ℂ) 0)) ∘ T)
    (-|C| - 1) (|C| + 1) (by linarith [abs_nonneg C])
    (fun y => (hψ.comp (by fun_prop)).of_le (by simp)) hline hsupp
    (polynomial_collision_real_first_slices d p hp F hF hd hg)
    (hMP.integrable_comp_of_integrable hgi) (hMP.integrable_comp_of_integrable hfi)
  rw [← hMP.integral_comp T.toHomeomorph.measurableEmbedding
      (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0) * θ z),
    ← hMP.integral_comp T.toHomeomorph.measurableEmbedding
      (fun z => F z * fderiv ℝ θ z (Fin.cons (1 : ℂ) 0))]
  exact h

end
end GinibrePoincare
