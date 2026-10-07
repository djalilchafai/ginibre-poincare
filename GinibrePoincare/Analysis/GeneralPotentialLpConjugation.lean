module

public import GinibrePoincare.Analysis.NonQuadraticBergmanComplex

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate InnerProductSpace
namespace GinibrePoincare
noncomputable section

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem complexLp_star_add (x y : Lp ℂ 2 μ) : star (x + y) = star x + star y := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (x+y), Lp.coeFn_star x, Lp.coeFn_star y,
    Lp.coeFn_add x y, Lp.coeFn_add (star x) (star y)] with z hs hx hy hxy hss
  rw [hs, hss]
  simp only [Pi.star_apply] at hx hy ⊢
  rw [hxy]
  simp only [Pi.add_apply]
  rw [hx, hy]
  simp

theorem complexLp_star_real_smul (a : ℝ) (x : Lp ℂ 2 μ) : star (a • x) = a • star x := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (a•x), Lp.coeFn_star x,
    Lp.coeFn_smul a x, Lp.coeFn_smul a (star x)] with z hs hx hax has
  rw [hs, has]
  simp only [Pi.star_apply, Pi.smul_apply] at hx hax ⊢
  rw [hax, hx]
  simp

theorem complexLp_norm_star (x : Lp ℂ 2 μ) : ‖star x‖ = ‖x‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  exact congrArg ENNReal.toReal AEEqFun.eLpNorm_star

/-- Genuine value conjugation as a real-linear isometry on arbitrary complex L². -/
def complexLpConjugationIsometry : Lp ℂ 2 μ →ₗᵢ[ℝ] Lp ℂ 2 μ where
  toFun := star
  map_add' := complexLp_star_add μ
  map_smul' := complexLp_star_real_smul μ
  norm_map' := complexLp_norm_star μ

/-- The actual antiunitary inner-product identity, for any source measure. -/
theorem complexLp_inner_star_star (x y : Lp ℂ 2 μ) :
    inner ℂ (star x) (star y) = conj (inner ℂ x y) := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  rw [integral_congr_ae (show
    (fun z => inner ℂ ((star x) z) ((star y) z)) =ᵐ[μ]
      (fun z => conj (inner ℂ (x z) (y z))) by
    filter_upwards [Lp.coeFn_star x, Lp.coeFn_star y] with z hx hy
    rw [hx, hy]
    simp [RCLike.inner_apply])]
  exact integral_conj

theorem complexLp_star_complex_smul (a : ℂ) (x : Lp ℂ 2 μ) :
    star (a • x) = conj a • star x := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (a•x), Lp.coeFn_smul a x, Lp.coeFn_star x,
    Lp.coeFn_smul (conj a) (star x)] with z hax hs hx ht
  rw [hax, ht]
  simp only [Pi.star_apply, Pi.smul_apply] at hs hx ⊢
  rw [hs, hx]
  simp

/-- Actual pullback commutes with value conjugation for arbitrary source measures. -/
theorem complexLp_compMeasurePreserving_star {Y : Type*} [MeasurableSpace Y]
    {ν : Measure Y} (f : X → Y) (hf : MeasurePreserving f μ ν) (x : Lp ℂ 2 ν) :
    Lp.compMeasurePreserving f hf (star x) = star (Lp.compMeasurePreserving f hf x) := by
  apply Lp.ext
  have hp := hf.quasiMeasurePreserving.ae_eq_comp (Lp.coeFn_star x)
  filter_upwards [Lp.coeFn_compMeasurePreserving (star x) hf,
    Lp.coeFn_compMeasurePreserving x hf, hp,
    Lp.coeFn_star (Lp.compMeasurePreserving f hf x)] with z hs hx hp ht
  change (Lp.compMeasurePreserving f hf (star x)) z = _
  change (Lp.compMeasurePreserving f hf (star x)) z = (star x) (f z) at hs
  change (Lp.compMeasurePreserving f hf x) z = x (f z) at hx
  change (star x) (f z) = star (x (f z)) at hp
  change (star (Lp.compMeasurePreserving f hf x)) z = star ((Lp.compMeasurePreserving f hf x) z) at ht
  rw [hs, ht, hp, hx]

#print axioms complexLp_inner_star_star
end
end GinibrePoincare
