module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalRegularityTestIntegrability
public import GinibrePoincare.Analysis.GinibreWeakGradient

@[expose] public section
open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000

theorem ginibreLocalRegularity_density_generator_pointwise
    (n : ℕ) (hn : 0 < n) (θ : Configuration n → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (z : Configuration n) (hz : CollisionFree z) :
    (n : ℝ)*ginibreLebesgueDensityReal n z*ginibrePregenerator n θ z =
      ginibreLebesgueDensityReal n z*(∑ k : Fin n × Fin 2,
        fderiv ℝ (fun y => fderiv ℝ θ y (ginibreCoordinateDirection k)) z (ginibreCoordinateDirection k)) +
      ∑ k : Fin n × Fin 2, fderiv ℝ (ginibreLebesgueDensityReal n) z (ginibreCoordinateDirection k)*
        fderiv ℝ θ z (ginibreCoordinateDirection k) := by
  have hprod (v : Configuration n) :
      fderiv ℝ (fun y => ginibreLebesgueDensityReal n y*fderiv ℝ θ y v) z v =
      ginibreLebesgueDensityReal n z*fderiv ℝ (fun y => fderiv ℝ θ y v) z v +
        fderiv ℝ (ginibreLebesgueDensityReal n) z v*fderiv ℝ θ z v := by
    have hd : ContDiff ℝ ∞ (fun y => fderiv ℝ θ y v) :=
      (hθ.fderiv_right (by simp)).clm_apply contDiff_const
    change fderiv ℝ ((ginibreLebesgueDensityReal n)*(fun y => fderiv ℝ θ y v)) z v = _
    rw [fderiv_mul ((contDiff_ginibreLebesgueDensityReal n).differentiable (by simp) z)
      (hd.differentiable (by simp) z)]
    simp only [smul_apply,add_apply,smul_eq_mul]
    ring
  have he := ginibreLebesgueDensityReal_mul_pregenerator_eq_divergence hn θ hθ z hz
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn0] at he
  rw [Fintype.sum_prod_type,Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,ginibreCoordinateDirection,ite_true,ite_false,one_ne_zero]
  simp_rw [hprod] at he
  rw [show (n : ℝ)*ginibreLebesgueDensityReal n z*ginibrePregenerator n θ z =
      ginibreLebesgueDensityReal n z*ginibrePregenerator n θ z*(n : ℝ) by ring,he,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

#print axioms ginibreLocalRegularity_density_generator_pointwise
end
end GinibrePoincare
