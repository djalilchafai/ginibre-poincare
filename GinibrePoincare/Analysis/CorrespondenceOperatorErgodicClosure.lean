module
public import GinibrePoincare.Analysis.CorrespondenceOperatorErgodicScalar
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
@[expose] public section
open Set Filter Metric
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- The continuous resolvent semigroup tends strongly to zero on the closure
of its complement range. No spectral gap or compactness is assumed. -/
theorem correspondenceOperator_ergodic_complement_closure
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H→L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀r∈spectrum ℝ R,r∈Icc (0:ℝ) 1)
    (x : H) (hx : x∈(1-R).range.topologicalClosure) :
    Tendsto (fun t : ℝ≥0 => resolventCfcEvolution R t x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hclos : x∈closure (Set.range ((1:H→L[ℂ] H)-R)) := by
    change x∈((1-R).range.topologicalClosure:Set H) at hx
    rw [Submodule.topologicalClosure_coe] at hx
    exact hx
  obtain ⟨z,hz,hzdist⟩ := Metric.mem_closure_iff.mp hclos (ε/2) (by positivity)
  obtain ⟨y,rfl⟩ := hz
  let T : ℝ≥0 := ⟨4*‖y‖/ε,by positivity⟩
  filter_upwards [eventually_ge_atTop T] with t ht
  have htR : 4*‖y‖≤ε*(t:ℝ) := by
    have hh : 4*‖y‖/ε≤(t:ℝ) := ht
    exact (div_le_iff₀ hε).mp hh |>.trans_eq (mul_comm _ _)
  have hsmall : (1/(1+(t:ℝ)))*‖y‖<ε/2 := by
    have hp : 0<1+(t:ℝ) := by positivity
    rw [one_div,mul_comm,← div_eq_mul_inv]
    apply (div_lt_iff₀ hp).mpr
    nlinarith [norm_nonneg y]
  have hbound : ‖resolventCfcEvolution R t ((1-R) y)‖≤(1/(1+(t:ℝ)))*‖y‖ :=
    ((resolventCfcEvolution R t*(1-R)).le_opNorm y).trans
      (mul_le_mul_of_nonneg_right (correspondenceOperator_ergodic_range_norm_bound R hR hSpec t)
        (norm_nonneg y))
  have hnear : dist (resolventCfcEvolution R t x) (resolventCfcEvolution R t ((1-R) y))≤
      dist x ((1-R) y) := by
    rw [dist_eq_norm,dist_eq_norm,← map_sub]
    exact resolventCfcEvolution_contracts R hSpec t _
  have htri := dist_triangle (resolventCfcEvolution R t x)
    (resolventCfcEvolution R t ((1-R) y)) 0
  rw [dist_zero_right] at htri ⊢
  have hd : dist x ((1-R) y)<ε/2 := by simpa only [dist_comm] using hzdist
  rw [dist_zero_right] at htri
  linarith
#print axioms correspondenceOperator_ergodic_complement_closure
end
end GinibrePoincare
