module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltEndpoint
public import GinibrePoincare.Analysis.BrownianIntegralGirsanovFiniteProductLaw

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Uniform refinement index with exactly `q * (n+1)` cells. -/
def brownianRationalRefinementIndex (q n : ℕ) := q*(n+1)-1

theorem brownianRationalRefinementIndex_succ (q n : ℕ) (hq : 0<q) :
    brownianRationalRefinementIndex q n+1=q*(n+1) := by
  exact Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.mul_pos hq (Nat.succ_pos n)))

theorem brownianRationalRefinementIndex_tendsto (q : ℕ) (hq : 0<q) :
    Tendsto (brownianRationalRefinementIndex q) atTop atTop := by
  apply tendsto_atTop_mono (fun n => ?_) tendsto_id
  have h := Nat.mul_le_mul_right (n+1) (Nat.succ_le_of_lt hq)
  change n ≤ q*(n+1)-1
  omega

/-- Exact alignment of a rational prefix with its own refined uniform mesh. -/
theorem brownianUniformNNTime_rational_prefix (T : ℝ≥0) (p q m k : ℕ)
    (hp : 0<p) (hq : 0<q) (hm : 0<m) :
    itoUniformNNTime T (q*m) k = itoUniformNNTime (T*(p:ℝ≥0)/(q:ℝ≥0)) (p*m) k := by
  apply NNReal.coe_injective
  simp only [itoUniformNNTime_coe,itoUniformTime,NNReal.coe_div,NNReal.coe_mul,
    NNReal.coe_natCast,Nat.cast_mul]
  have hp' : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
  have hq' : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hm' : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  <;> ring

theorem brownianUniformNNTime_rational_endpoint (T : ℝ≥0) (p q m : ℕ)
    (hq : 0<q) (hm : 0<m) :
    itoUniformNNTime T (q*m) (p*m)=T*(p:ℝ≥0)/(q:ℝ≥0) := by
  apply NNReal.coe_injective
  simp only [itoUniformNNTime_coe,itoUniformTime,NNReal.coe_div,NNReal.coe_mul,
    NNReal.coe_natCast,Nat.cast_mul]
  have hq' : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
  have hm' : (m:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hm)
  field_simp
  <;> ring

/-- Actual partial drift Riemann sums converge at every rational subdivision
of the fixed terminal horizon. -/
theorem brownianRationalPrefix_drift_tendsto (T : ℝ≥0) (p q : ℕ)
    (hp : 0<p) (hq : 0<q) (F : ℝ≥0 → ℝ)
    (hc : ContinuousOn F (Set.Icc 0 (T*(p:ℝ≥0)/(q:ℝ≥0)))) :
    Tendsto (fun n => ∑ k ∈ Finset.range (p*(n+1)),
      F (itoUniformNNTime T (q*(n+1)) k)*((T:ℝ)/(q*(n+1):ℕ))) atTop
      (𝓝 (∫ s in (0:ℝ)..(T*(p:ℝ≥0)/(q:ℝ≥0):ℝ≥0), F (Real.toNNReal s))) := by
  let t := T*(p:ℝ≥0)/(q:ℝ≥0)
  have hfc : ContinuousOn (fun s : ℝ => F (Real.toNNReal s)) (Set.Icc 0 (t:ℝ)) :=
    hc.comp continuous_real_toNNReal.continuousOn (by
      intro s hs
      exact ⟨by positivity,by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2⟩)
  have ht := (itoContinuousScalarRiemann_fin_tendsto (fun s : ℝ => F (Real.toNNReal s)) t hfc).comp
    (brownianRationalRefinementIndex_tendsto p hp)
  have heq (n : ℕ) :
      (∑ k : Fin (brownianRationalRefinementIndex p n+1),
        F (Real.toNNReal (ginibreUniformBrownianTime t (brownianRationalRefinementIndex p n) k))*
        ((t:ℝ)/((brownianRationalRefinementIndex p n:ℝ)+1))) =
      ∑ k ∈ Finset.range (p*(n+1)), F (itoUniformNNTime T (q*(n+1)) k)*((T:ℝ)/(q*(n+1):ℕ)) := by
    simp only [Real.toNNReal_coe]
    rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => F (ginibreUniformBrownianTime t
      (brownianRationalRefinementIndex p n) k)*((t:ℝ)/((brownianRationalRefinementIndex p n:ℝ)+1)))
      (brownianRationalRefinementIndex p n+1)]
    simp_rw [← itoUniformNNTime_eq_ginibreUniformBrownianTime,
      brownianRationalRefinementIndex_succ p n hp]
    apply Finset.sum_congr rfl
    intro k hk
    rw [brownianUniformNNTime_rational_prefix T p q (n+1) k hp hq (Nat.succ_pos n)]
    congr 1
    have hi := congrArg (fun m : ℕ => (m:ℝ)) (brownianRationalRefinementIndex_succ p n hp)
    simp only [Nat.cast_add,Nat.cast_one,Nat.cast_mul] at hi
    rw [hi]
    dsimp only [t]
    simp only [NNReal.coe_div,NNReal.coe_mul,NNReal.coe_natCast,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    have hp' : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hp)
    have hq' : (q:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hq)
    have hn' : (n:ℝ)+1≠0 := by positivity
    field_simp
    <;> ring
  simpa only [Function.comp_def,heq] using ht

end
end GinibrePoincare
