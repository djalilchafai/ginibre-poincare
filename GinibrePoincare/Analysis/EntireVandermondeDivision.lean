module

public import GinibrePoincare.Analysis.GaussianEntireRepresentatives

@[expose] public section

/-! # Pointwise obligations for entire Vandermonde division

This file proves the vanishing, uniqueness, and symmetry obligations for
entire division. Existence across the collision hyperplanes is a separate
analytic theorem, and is not asserted here.
-/

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- An alternating function vanishes on every collision hyperplane. -/
theorem alternating_function_eq_zero_on_collision {n : ℕ}
    {f : Configuration n → ℂ} (hf : IsAlternating f)
    {z : Configuration n} (hz : z ∈ collisionSet n) : f z = 0 := by
  obtain ⟨i, j, hij, hne⟩ := hz
  have hp : permute (Equiv.swap i j) z = z := by
    ext k
    by_cases hki : k = i
    · subst k; simp [permute, hij]
    · by_cases hkj : k = j
      · subst k; simp [permute, hij]
      · simp [permute, Equiv.swap_apply_of_ne_of_ne hki hkj]
  have he := hf (Equiv.swap i j) z
  rw [hp] at he
  have hs : permutationSign (Equiv.swap i j) = -1 := by
    simp [permutationSign, hne]
  rw [hs] at he
  have htwo : (2 : ℂ) * f z = 0 := by linear_combination he
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- An entire representative of an alternating Gaussian class vanishes
pointwise at every collision, not merely almost everywhere. -/
theorem gaussianEntireRepresentative_eq_zero_on_collision {n : ℕ}
    (hn : 0 < n) {u : Lp ℂ 2 (complexGaussianMeasure n)}
    (hu : u ∈ gaussianAlternatingL2 n) {f : Configuration n → ℂ}
    (hf : IsGaussianEntireRepresentative u f) {z : Configuration n}
    (hz : z ∈ collisionSet n) : f z = 0 :=
  alternating_function_eq_zero_on_collision
    (gaussianEntireRepresentative_alternating hn hu hf) hz

/-- Any two continuous extensions of a Vandermonde quotient agree globally. -/
theorem continuous_vandermonde_quotient_unique {n : ℕ} (hn : 0 < n)
    {f g h : Configuration n → ℂ} (hg : Continuous g) (hh : Continuous h)
    (hfg : ∀ z, f z = vandermonde z * g z)
    (hfh : ∀ z, f z = vandermonde z * h z) : g = h := by
  apply continuous_eq_of_ae_eq_complexGaussian hn hg hh
  have hcf : ∀ᵐ z ∂complexGaussianMeasure n, z ∉ collisionSet n := by
    rw [ae_iff]
    simp only [not_not]
    exact complexGaussianMeasure_collisionSet n
  filter_upwards [hcf] with z hz
  apply mul_left_cancel₀ (fun hv => hz ((vandermonde_eq_zero_iff z).mp hv))
  exact (hfg z).symm.trans (hfh z)

/-- A continuous global quotient of an alternating function is symmetric. -/
theorem continuous_vandermonde_quotient_symmetric {n : ℕ} (hn : 0 < n)
    {f g : Configuration n → ℂ} (hf : IsAlternating f) (hg : Continuous g)
    (hfg : ∀ z, f z = vandermonde z * g z) : IsSymmetric g := by
  intro σ z
  have hc : Continuous (permute σ : Configuration n → Configuration n) :=
    continuous_pi (fun i => continuous_apply (σ i))
  have hfac : ∀ w, f w = vandermonde w * g (permute σ w) := by
    intro w
    have he := hf σ w
    rw [hfg (permute σ w), hfg w, vandermonde_permute] at he
    have hs : permutationSign σ ≠ 0 := by
      unfold permutationSign
      norm_num
    apply mul_left_cancel₀ hs
    rw [hfg w]
    simpa only [mul_assoc] using he.symm
  exact congrFun (continuous_vandermonde_quotient_unique hn (hg.comp hc) hg hfac hfg) z

#print axioms alternating_function_eq_zero_on_collision
#print axioms gaussianEntireRepresentative_eq_zero_on_collision
#print axioms continuous_vandermonde_quotient_unique
#print axioms continuous_vandermonde_quotient_symmetric

end
end GinibrePoincare
