module

public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryMonomialMultilinear
public import GinibrePoincare.Analysis.GaussianEntireSeriesBounds
public import Mathlib.Analysis.Analytic.ChangeOrigin
public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

@[expose] public section
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual homogeneous-degree grouping of the normalized holomorphic
Hermite reconstruction into continuous multilinear Taylor coefficients. -/
def holomorphicHermiteFormalSeries (n : ℕ) (c : (Fin n → ℕ) → ℂ) :
    FormalMultilinearSeries ℂ (Configuration n) ℂ := fun k => by
  letI := (finite_holomorphic_degree_fiber n k).fintype
  exact ∑ p : {p : Fin n → ℕ | ∑ i, p i = k},
    (c p.val * ∏ i, (ComplexHermite.oneDimNormalization n (p.val i) : ℂ)) •
      (holomorphicMonomialMultilinear p.val).domDomCongr (finCongr p.property)

/-- Its homogeneous diagonal is exactly the finite degree slice of the
original normalized Hermite series. -/
theorem holomorphicHermiteFormalSeries_diagonal (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) (k : ℕ) (z : Configuration n) :
    holomorphicHermiteFormalSeries n c k (fun _ => z) =
      ∑ p ∈ (finite_holomorphic_degree_fiber n k).toFinset,
        c p * ComplexHermite.multivariateNormalized n hn p 0 z := by
  letI := (finite_holomorphic_degree_fiber n k).fintype
  unfold holomorphicHermiteFormalSeries
  simp only [ContinuousMultilinearMap.sum_apply,ContinuousMultilinearMap.smul_apply,
    ContinuousMultilinearMap.domDomCongr_apply,Function.comp_def,smul_eq_mul,
    holomorphicMonomialMultilinear_diagonal]
  rw [Finset.sum_subtype (p := fun p : Fin n → ℕ => ∑ i, p i = k)
    (finite_holomorphic_degree_fiber n k).toFinset (by simp)
    (fun p => c p * ComplexHermite.multivariateNormalized n hn p 0 z)]
  apply Finset.sum_congr rfl
  intro p hp
  rw [ComplexHermite.multivariateNormalized_zero_right,Finset.prod_mul_distrib]
  ring

theorem holomorphicHermiteFormalSeries_norm_le (n : ℕ)
    (c : (Fin n → ℕ) → ℂ) (k : ℕ) :
    ‖holomorphicHermiteFormalSeries n c k‖ ≤
      ∑ p ∈ (finite_holomorphic_degree_fiber n k).toFinset,
        ‖c p‖ * ∏ i, ComplexHermite.oneDimNormalization n (p i) := by
  letI := (finite_holomorphic_degree_fiber n k).fintype
  unfold holomorphicHermiteFormalSeries
  rw [Finset.sum_subtype (p := fun p : Fin n → ℕ => ∑ i, p i = k)
    (finite_holomorphic_degree_fiber n k).toFinset (by simp)
    (fun p => ‖c p‖ * ∏ i, ComplexHermite.oneDimNormalization n (p i))]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_smul,ContinuousMultilinearMap.norm_domDomCongr,norm_mul,norm_prod]
  have hnorm : ∏ i, ‖(ComplexHermite.oneDimNormalization n (p.val i) : ℂ)‖ =
      ∏ i, ComplexHermite.oneDimNormalization n (p.val i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg]
    unfold ComplexHermite.oneDimNormalization
    positivity
  rw [hnorm]
  exact mul_le_of_le_one_right (by unfold ComplexHermite.oneDimNormalization; positivity) (holomorphicMonomialMultilinear_norm_le _)

/-- Bounded Hermite coefficients yield an infinite-radius genuine
multivariate Taylor series, with no analyticity assumption. -/
theorem holomorphicHermiteFormalSeries_radius (n : ℕ)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C) :
    (holomorphicHermiteFormalSeries n c).radius = ⊤ := by
  apply FormalMultilinearSeries.radius_eq_top_of_summable_norm
  intro r
  let B : (Fin n → ℕ) → ℝ := fun p =>
    C * ∏ i, ComplexHermite.oneDimNormalization n (p i) * (r : ℝ) ^ p i
  have hs : Summable B :=
    (summable_tensor_holomorphicHermite_bound n n r.coe_nonneg).mul_left C
  have hg : Summable (fun k => ∑ p ∈ (finite_holomorphic_degree_fiber n k).toFinset, B p) := by
    have hh := (hs.hasSum.tsum_fiberwise (fun p => ∑ i, p i)).summable
    convert hh using 1
    funext k
    letI : Fintype {p : Fin n → ℕ // ∑ i, p i = k} :=
      (finite_holomorphic_degree_fiber n k).fintype
    rw [Finset.sum_subtype (p := fun p : Fin n → ℕ => ∑ i, p i = k)
      (finite_holomorphic_degree_fiber n k).toFinset (by simp) B]
    change (∑ p : {p : Fin n → ℕ // ∑ i, p i = k}, B p.val) =
      ∑' p : {p : Fin n → ℕ // ∑ i, p i = k}, B p.val
    letI : Fintype {p : Fin n → ℕ // ∑ i, p i = k} :=
      (finite_holomorphic_degree_fiber n k).fintype
    exact (tsum_fintype _).symm
  apply Summable.of_nonneg_of_le (fun k => by positivity) _ hg
  intro k
  apply (mul_le_mul_of_nonneg_right (holomorphicHermiteFormalSeries_norm_le n c k)
    (by positivity)).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hpk : ∑ i, p i = k := (finite_holomorphic_degree_fiber n k).mem_toFinset.mp hp
  unfold B
  rw [Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum,hpk]
  have hpnon : 0 ≤ ∏ i, ComplexHermite.oneDimNormalization n (p i) := by
    unfold ComplexHermite.oneDimNormalization
    positivity
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (hC p) hpnon) (show 0 ≤ (r : ℝ)^k by positivity)

theorem holomorphicHermiteFormalSeries_sum (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (z : Configuration n) :
    (holomorphicHermiteFormalSeries n c).sum z =
      ∑' p, c p * ComplexHermite.multivariateNormalized n hn p 0 z := by
  have hs := summable_holomorphicHermite_series n hn c hC z
  have hg := hs.hasSum.tsum_fiberwise (fun p => ∑ i, p i)
  unfold FormalMultilinearSeries.sum
  convert hg.tsum_eq using 1
  congr 1
  funext k
  rw [holomorphicHermiteFormalSeries_diagonal n hn c k z]
  letI : Fintype {p : Fin n → ℕ // ∑ i, p i = k} :=
    (finite_holomorphic_degree_fiber n k).fintype
  rw [Finset.sum_subtype (p := fun p : Fin n → ℕ => ∑ i, p i = k)
    (finite_holomorphic_degree_fiber n k).toFinset (by simp)
    (fun p => c p * ComplexHermite.multivariateNormalized n hn p 0 z)]
  change (∑ p : {p : Fin n → ℕ // ∑ i, p i = k},
    c p.val * ComplexHermite.multivariateNormalized n hn p.val 0 z) =
      ∑' p : {p : Fin n → ℕ // ∑ i, p i = k},
        c p.val * ComplexHermite.multivariateNormalized n hn p.val 0 z
  exact (tsum_fintype _).symm

/-- The actual bounded-coefficient Gaussian holomorphic reconstruction is
jointly real analytic in all coordinates. -/
theorem holomorphicHermite_series_real_analytic (n : ℕ) (hn : 0 < n)
    (c : (Fin n → ℕ) → ℂ) {C : ℝ} (hC : ∀ p, ‖c p‖ ≤ C)
    (z : Configuration n) :
    AnalyticAt ℝ (fun w => ∑' p,
      c p * ComplexHermite.multivariateNormalized n hn p 0 w) z := by
  have h := (holomorphicHermiteFormalSeries n c).analyticOnNhd
  have hr := holomorphicHermiteFormalSeries_radius n c hC
  have ha : AnalyticAt ℂ (holomorphicHermiteFormalSeries n c).sum z :=
    h z (by simp [hr])
  have he : (holomorphicHermiteFormalSeries n c).sum =
      (fun w => ∑' p, c p * ComplexHermite.multivariateNormalized n hn p 0 w) :=
    funext (holomorphicHermiteFormalSeries_sum n hn c hC)
  rw [he] at ha
  exact ha.restrictScalars

#print axioms holomorphicHermiteFormalSeries_sum
#print axioms holomorphicHermite_series_real_analytic
#print axioms holomorphicHermiteFormalSeries_radius
#print axioms holomorphicHermiteFormalSeries_norm_le
#print axioms holomorphicHermiteFormalSeries_diagonal
end
end GinibrePoincare
