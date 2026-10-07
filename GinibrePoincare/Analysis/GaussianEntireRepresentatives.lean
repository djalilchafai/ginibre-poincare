module

public import GinibrePoincare.Analysis.L2RepresentativeBridges

@[expose] public section

/-! # Genuine entire Gaussian representatives

Here `Differentiable ℂ` means holomorphic on the whole configuration space.
These results upgrade almost-everywhere permutation identities to identities
at every point. They do not assert existence of an entire representative.
-/

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- An actual entire representative of a Gaussian square-integrable class. -/
def IsGaussianEntireRepresentative {n : ℕ}
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (f : Configuration n → ℂ) : Prop :=
  Differentiable ℂ f ∧ f =ᵐ[complexGaussianMeasure n] u

/-- Entire representatives are unique as functions, including on collisions. -/
theorem gaussianEntireRepresentative_unique {n : ℕ} (hn : 0 < n)
    {u : Lp ℂ 2 (complexGaussianMeasure n)} {f g : Configuration n → ℂ}
    (hf : IsGaussianEntireRepresentative u f)
    (hg : IsGaussianEntireRepresentative u g) : f = g :=
  continuous_eq_of_ae_eq_complexGaussian hn hf.1.continuous hg.1.continuous
    (hf.2.trans hg.2.symm)

/-- A continuous representative of an alternating Gaussian class is pointwise
alternating, so the collision values cannot be chosen independently. -/
theorem continuous_gaussianAlternating_representative {n : ℕ} (hn : 0 < n)
    {u : Lp ℂ 2 (complexGaussianMeasure n)} (hu : u ∈ gaussianAlternatingL2 n)
    {f : Configuration n → ℂ} (hf : Continuous f)
    (hfu : f =ᵐ[complexGaussianMeasure n] u) : IsAlternating f := by
  intro σ z
  have hcomp := (gaussian_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hfu
  have hp := Lp.coeFn_compMeasurePreserving u (gaussian_measurePreserving_permute σ)
  have hs := Lp.coeFn_smul (permutationSign σ) u
  have heq : (fun z => f (permute σ z)) =ᵐ[complexGaussianMeasure n]
      (fun z => permutationSign σ * f z) := by
    filter_upwards [hcomp, hp, hs, hfu] with w hw hpw hsw hfw
    change f (permute σ w) = u (permute σ w) at hw
    change (gaussianPermutationL2 σ u) w = u (permute σ w) at hpw
    rw [hw, ← hpw]
    rw [hu σ, hsw]
    change permutationSign σ * u w = permutationSign σ * f w
    rw [hfw]
  have hc : Continuous (permute σ : Configuration n → Configuration n) :=
    continuous_pi (fun i => continuous_apply (σ i))
  exact congrFun (continuous_eq_of_ae_eq_complexGaussian hn (hf.comp hc)
    (continuous_const.mul hf) heq) z

theorem gaussianEntireRepresentative_alternating {n : ℕ} (hn : 0 < n)
    {u : Lp ℂ 2 (complexGaussianMeasure n)} (hu : u ∈ gaussianAlternatingL2 n)
    {f : Configuration n → ℂ} (hf : IsGaussianEntireRepresentative u f) :
    IsAlternating f :=
  continuous_gaussianAlternating_representative hn hu hf.1.continuous hf.2

/-- The Gaussian classes admitting actual entire representatives form a
complex submodule. No closed-span definition is used. -/
def gaussianEntireL2 (n : ℕ) : Submodule ℂ (Lp ℂ 2 (complexGaussianMeasure n)) where
  carrier := {u | ∃ f, IsGaussianEntireRepresentative u f}
  zero_mem' := by
    refine ⟨0, differentiable_const 0, ?_⟩
    exact (Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)).symm
  add_mem' := by
    rintro u v ⟨f, hf⟩ ⟨g, hg⟩
    refine ⟨fun z => f z + g z, hf.1.add hg.1, ?_⟩
    filter_upwards [hf.2, hg.2, Lp.coeFn_add u v] with z hz hz' hz''
    simp only [hz, hz']
    exact hz''.symm
  smul_mem' := by
    rintro c u ⟨f, hf⟩
    refine ⟨fun z => c * f z, differentiable_const c |>.mul hf.1, ?_⟩
    filter_upwards [hf.2, Lp.coeFn_smul c u] with z hz hz'
    simpa only [hz, Pi.smul_apply, smul_eq_mul] using hz'.symm

theorem mem_gaussianEntireL2_iff {n : ℕ}
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    u ∈ gaussianEntireL2 n ↔ ∃ f : Configuration n → ℂ,
      Differentiable ℂ f ∧ f =ᵐ[complexGaussianMeasure n] u := Iff.rfl

theorem gaussianEntireL2_unique_representative {n : ℕ} (hn : 0 < n)
    {u : Lp ℂ 2 (complexGaussianMeasure n)} (hu : u ∈ gaussianEntireL2 n) :
    ∃! f : Configuration n → ℂ, IsGaussianEntireRepresentative u f := by
  obtain ⟨f, hf⟩ := hu
  exact ⟨f, hf, fun g hg => gaussianEntireRepresentative_unique hn hg hf⟩

#print axioms gaussianEntireRepresentative_unique
#print axioms gaussianEntireRepresentative_alternating
#print axioms gaussianEntireL2_unique_representative

end
end GinibrePoincare
