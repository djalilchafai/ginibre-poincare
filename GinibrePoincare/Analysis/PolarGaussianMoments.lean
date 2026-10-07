module

public import GinibrePoincare.Analysis.AngularMoments
public import GinibrePoincare.Analysis.RadialMoments
public import GinibrePoincare.Analysis.ComplexGaussianDensity
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # Polar factorization of complex Gaussian moments -/

open MeasureTheory Set
open scoped ComplexConjugate Real

namespace GinibrePoincare

noncomputable section

/-- The complex monomial separates into a radial power and an angular Fourier
mode in polar coordinates. -/
theorem mixedMonomial_polar (a b : ℕ) (r θ : ℝ) :
    (Complex.polarCoord.symm (r, θ)) ^ a *
        conj (Complex.polarCoord.symm (r, θ)) ^ b =
      (r ^ (a + b) : ℂ) * angularMode a b θ := by
  rw [Complex.polarCoord_symm_apply]
  rw [show (Real.cos θ + Real.sin θ * Complex.I) =
      Complex.exp (θ * Complex.I) by
    rw [Complex.exp_mul_I]
    push_cast
    ring]
  simp only [mul_pow, map_mul, Complex.conj_ofReal]
  rw [show conj (Complex.exp (θ * Complex.I)) =
      Complex.exp (-(θ * Complex.I)) by
    rw [← Complex.exp_conj]
    congr 1
    simp]
  unfold angularMode
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
  calc
    _ = (r ^ (a + b) : ℂ) *
        (Complex.exp ((a : ℂ) * (θ * Complex.I)) *
          Complex.exp ((b : ℂ) * -(θ * Complex.I))) := by
      rw [pow_add]
      ring
    _ = (r ^ (a + b) : ℂ) *
        Complex.exp ((a : ℂ) * (θ * Complex.I) +
          (b : ℂ) * -(θ * Complex.I)) := by rw [Complex.exp_add]
    _ = _ := by
      congr 2
      push_cast
      ring

/-- The Jacobian, Gaussian density, and mixed monomial separate into a radial
factor and the angular Fourier mode.  This formulation makes all real-to-
complex coercions explicit, avoiding expensive elaboration inside an
integral. -/
theorem gaussianMixedIntegrand_polar (n a b : ℕ) (r θ : ℝ) :
    r • (((n : ℝ) / Real.pi) * Real.exp (-(n : ℝ) * r ^ 2)) •
        ((Complex.polarCoord.symm (r, θ)) ^ a *
          conj (Complex.polarCoord.symm (r, θ)) ^ b) =
      ((r : ℂ) *
        ((((n : ℝ) : ℂ) / Real.pi) *
          (Real.exp (-(n : ℝ) * r ^ 2) : ℂ)) *
        (r : ℂ) ^ (a + b)) * angularMode a b θ := by
  rw [mixedMonomial_polar]
  simp only [Algebra.smul_def, RCLike.algebraMap_eq_ofReal]
  have hd : ((((n : ℝ) / Real.pi) * Real.exp (-(n : ℝ) * r ^ 2) : ℝ) : ℂ) =
      (((n : ℝ) : ℂ) / Real.pi) *
        (Real.exp (-(n : ℝ) * r ^ 2) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_div]
  change (r : ℂ) *
      (((((n : ℝ) / Real.pi) * Real.exp (-(n : ℝ) * r ^ 2) : ℝ) : ℂ) *
        ((r : ℂ) ^ (a + b) * angularMode a b θ)) = _
  rw [hd]
  simp only [mul_assoc]

/-- Fubini factorization for the separated polar Gaussian mixed-moment
integrand. -/
theorem integral_gaussianMixedIntegrand_polar (n a b : ℕ) :
    ∫ p : ℝ × ℝ in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((((n : ℝ) : ℂ) / Real.pi) * (p.1 : ℂ) ^ (a + b + 1) *
          (Real.exp (-(n : ℝ) * p.1 ^ 2) : ℂ)) * angularMode a b p.2 =
      (∫ r : ℝ in Set.Ioi 0,
          (((n : ℝ) : ℂ) / Real.pi) * (r : ℂ) ^ (a + b + 1) *
            (Real.exp (-(n : ℝ) * r ^ 2) : ℂ)) *
        ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi, angularMode a b θ := by
  rw [Measure.volume_eq_prod]
  simpa only [mul_assoc] using
    (setIntegral_prod_mul
      (fun r : ℝ ↦ (((n : ℝ) : ℂ) / Real.pi) * (r : ℂ) ^ (a + b + 1) *
        (Real.exp (-(n : ℝ) * r ^ 2) : ℂ))
      (angularMode a b) (Set.Ioi 0) (Set.Ioo (-Real.pi) Real.pi))

/-- The angular evaluation in the open interval used by `polarCoord.target`. -/
theorem integral_angularMode_Ioo (a b : ℕ) :
    ∫ θ : ℝ in Set.Ioo (-Real.pi) Real.pi, angularMode a b θ =
      if a = b then (2 * Real.pi : ℂ) else 0 := by
  rw [← integral_Ioc_eq_integral_Ioo]
  exact integral_angularMode_Ioc a b

/-- Exact evaluation of the separated Gaussian mixed integrand on the polar
coordinate target. -/
theorem integral_gaussianMixedIntegrand_polar_eq (n a b : ℕ) (hn : 0 < n) :
    ∫ p : ℝ × ℝ in Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi,
        ((((n : ℝ) : ℂ) / Real.pi) * (p.1 : ℂ) ^ (a + b + 1) *
          (Real.exp (-(n : ℝ) * p.1 ^ 2) : ℂ)) * angularMode a b p.2 =
      if a = b then (a.factorial : ℂ) / (n : ℂ) ^ a else 0 := by
  rw [integral_gaussianMixedIntegrand_polar, integral_angularMode_Ioo]
  by_cases hab : a = b
  · subst b
    simp only [if_pos]
    have hrad := integral_pow_mul_exp_neg_mul_sq_Ioi_complex n a hn
    rw [show a + a + 1 = 2 * a + 1 by omega]
    have hint :
        (∫ r : ℝ in Set.Ioi 0,
            (((n : ℝ) : ℂ) / Real.pi) * (r : ℂ) ^ (2 * a + 1) *
              (Real.exp (-(n : ℝ) * r ^ 2) : ℂ)) =
          (((n : ℝ) : ℂ) / Real.pi) *
            ∫ r : ℝ in Set.Ioi 0,
              ((r ^ (2 * a + 1) * Real.exp (-(n : ℝ) * r ^ 2) : ℝ) : ℂ) := by
      calc
        _ = ∫ r : ℝ in Set.Ioi 0,
            (((n : ℝ) : ℂ) / Real.pi) *
              ((r ^ (2 * a + 1) * Real.exp (-(n : ℝ) * r ^ 2) : ℝ) : ℂ) := by
                apply integral_congr_ae
                filter_upwards with r
                push_cast
                ring
        _ = _ := integral_const_mul
          (((n : ℝ) : ℂ) / Real.pi)
          (fun r : ℝ ↦
            ((r ^ (2 * a + 1) * Real.exp (-(n : ℝ) * r ^ 2) : ℝ) : ℂ))
    rw [hint, hrad]
    field_simp [show (n : ℂ) ≠ 0 by exact_mod_cast hn.ne']
    rw [pow_succ]
    push_cast
    simp only [mul_comm, mul_left_comm, mul_assoc]
  · simp only [if_neg hab, mul_zero]

end

end GinibrePoincare
