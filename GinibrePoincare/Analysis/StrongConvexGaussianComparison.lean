module

public import GinibrePoincare.Analysis.StrongConvexGaussianProfile
public import GinibrePoincare.Analysis.StrongConvexDensityComparison

@[expose] public section

open Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

theorem density_profile_dominates_gaussian (h : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hc : ContinuousOn h (Icc 0 1)) (h0 : 0 ≤ h 0) (h1 : 0 ≤ h 1)
    (hd : ∀ u ∈ Ioo 0 1, ContDiffAt ℝ 2 h u)
    (hp : ∀ u ∈ Ioo 0 1, 0 < h u)
    (hdd : ∀ u ∈ Ioo 0 1, deriv (deriv h) u ≤ -κ / h u) :
    ∀ u ∈ Icc 0 1, Real.sqrt κ * standardGaussianDensityProfile u ≤ h u := by
  let j := fun u => Real.sqrt κ * standardGaussianDensityProfile u
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  apply positive_density_profile_comparison h j 0 1 κ (by norm_num) hκ hc
    (standardGaussianDensityProfile_continuousOn.const_mul _)
  · simpa [j, standardGaussianDensityProfile, densityQuantileProfile] using h0
  · simpa [j, standardGaussianDensityProfile, densityQuantileProfile] using h1
  · exact hd
  · intro u hu
    exact contDiffAt_const.mul (standardGaussianDensityProfile_contDiffAt u hu)
  · exact hp
  · intro u hu
    exact mul_pos hs (standardGaussianDensityProfile_pos u hu)
  · exact hdd
  · intro u hu
    have he : deriv (deriv j) u = Real.sqrt κ *
        deriv (deriv standardGaussianDensityProfile) u := by
      simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
        (iteratedDeriv_const_mul (n := 2) (Real.sqrt κ)
          (standardGaussianDensityProfile_contDiffAt u hu))
    rw [he, standardGaussianDensityProfile_second_derivative u hu]
    have hi := (standardGaussianDensityProfile_pos u hu).ne'
    have hs2 := Real.sq_sqrt hκ.le
    dsimp [j]
    field_simp
    nlinarith

end
end GinibrePoincare
