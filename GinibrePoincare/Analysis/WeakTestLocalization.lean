module

public import GinibrePoincare.Analysis.SmoothTestLocalization
public import GinibrePoincare.Analysis.GinibreWeakGradientPhase

@[expose] public section

/-! # Gluing actual ordinary weak derivative identities on open patches -/

open MeasureTheory
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section

/-- Ordinary weak derivative tests glue across any open cover of an open set. -/
theorem weak_derivative_test_of_open_cover (n : ℕ)
    (U : Set (Configuration n)) (hU : IsOpen U)
    (u w : Configuration n → ℝ) (hu : LocallyIntegrableOn u U volume)
    (hw : LocallyIntegrableOn w U volume) (v : Configuration n)
    {ι : Type*} (V : ι → Set (Configuration n)) (hV : ∀ i, IsOpen (V i))
    (hVU : ∀ i, V i ⊆ U) (hcover : U ⊆ ⋃ i, V i)
    (htest : ∀ i θ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ V i →
      (∫ z, w z * θ z) = -(∫ z, u z * fderiv ℝ θ z v))
    (θ : Configuration n → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ U) :
    (∫ z, w z * θ z) = -(∫ z, u z * fderiv ℝ θ z v) := by
  classical
  obtain ⟨I, ψ, hψ, he⟩ := exists_finite_smooth_test_decomposition θ hθ hc V hV
    (hs.trans hcover)
  have hi (i : ι) : Integrable (fun z => w z * ψ i z) :=
    integrable_mul_open_compact_test n U hU w (ψ i) hw (hψ i).1.continuous
      (hψ i).2.1 ((hψ i).2.2.trans (hVU i))
  have hj (i : ι) : Integrable (fun z => u z * fderiv ℝ (ψ i) z v) :=
    integrable_mul_open_compact_test n U hU u _ hu
      (((hψ i).1.continuous_fderiv (by simp)).clm_apply continuous_const)
      ((hψ i).2.1.fderiv_apply ℝ v)
      ((tsupport_fderiv_apply_subset ℝ v).trans ((hψ i).2.2.trans (hVU i)))
  have hd (z : Configuration n) : fderiv ℝ θ z v =
      ∑ i ∈ I, fderiv ℝ (ψ i) z v := by
    rw [he, fderiv_fun_sum (fun i _ => ((hψ i).1.differentiable (by simp)).differentiableAt)]
    simp only [ContinuousLinearMap.sum_apply]
  calc
    _ = ∑ i ∈ I, ∫ z, w z * ψ i z := by
      conv_lhs => rw [he]
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum I (fun i _ => hi i)
    _ = ∑ i ∈ I, -(∫ z, u z * fderiv ℝ (ψ i) z v) := by
      apply Finset.sum_congr rfl
      intro i _
      exact htest i (ψ i) (hψ i).1 (hψ i).2.1 (hψ i).2.2
    _ = -(∫ z, u z * fderiv ℝ θ z v) := by
      simp_rw [hd, Finset.mul_sum]
      rw [integral_finsetSum I (fun i _ => hj i), Finset.sum_neg_distrib]

end
end GinibrePoincare
