module
public import GinibrePoincare.Analysis.CorrespondenceOperatorComplexHermiteMultiplier
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberSelfAdjoint
public import Mathlib.Order.Filter.IsBounded
@[expose] public section
open MeasureTheory Filter Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem correspondenceOperatorNumber_inverse_weights_bounded (n : ℕ) (hn : 0<n) (z : ℂ) :
    ∃M : ℝ,0<M ∧ ∀k : ℕ,‖(((n*k:ℕ):ℂ)-z)⁻¹‖≤M := by
  obtain ⟨K,hK⟩ := exists_nat_gt (‖z‖+1)
  have ht : ∀ᶠ k : ℕ in atTop,‖(((n*k:ℕ):ℂ)-z)⁻¹‖≤1 := by
    filter_upwards [eventually_ge_atTop K] with k hk
    have hnk : K≤n*k := le_trans hk (Nat.le_mul_of_pos_left k hn)
    have hv : ‖z‖+1<((n*k:ℕ):ℝ) := lt_of_lt_of_le hK (by exact_mod_cast hnk)
    have hl : 1≤‖((n*k:ℕ):ℂ)-z‖ := by
      have hh := norm_sub_norm_le (((n*k:ℕ):ℂ)) z
      rw [Complex.norm_natCast] at hh
      linarith
    rw [norm_inv]
    exact (inv_le_one₀ (by linarith : 0<‖((n*k:ℕ):ℂ)-z‖)).mpr hl
  obtain ⟨M,hM⟩ := (isBoundedUnder_of_eventually_le ht).bddAbove_range
  refine ⟨max 1 M,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro k
  exact le_trans (hM (mem_range_self k)) (le_max_right _ _)

/-- The genuine unbounded resolvent condition: a bounded map is a two-sided
inverse to the literal maximal differential graph shifted by z. -/
def correspondenceOperatorNumberHasResolvent (n : ℕ) (hn : 0<n) (z : ℂ) : Prop :=
  ∃R : Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n),
    (∀f,(R f,f+z • R f)∈(correspondenceOperatorNumber n hn).graph) ∧
    (∀u v,(u,v)∈(correspondenceOperatorNumber n hn).graph→R (v-z • u)=u)

/-- Every complex number outside the literal nℕ eigenvalues has a genuine
bounded two-sided resolvent on the full maximal operator domain. -/
theorem correspondenceOperatorNumber_resolvent_outside (n : ℕ) (hn : 0<n) (z : ℂ)
    (hz : ∀k : ℕ,z≠((n*k:ℕ):ℂ)) : correspondenceOperatorNumberHasResolvent n hn z := by
  obtain ⟨M,hM,hbound⟩ := correspondenceOperatorNumber_inverse_weights_bounded n hn z
  let w : HermiteMultiIndex n→ℂ := fun pq=>(((n*totalAntiDegree pq:ℕ):ℂ)-z)⁻¹/(M:ℂ)
  have hw : ∀pq,‖w pq‖≤1 := by
    intro pq
    dsimp [w]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
    exact (div_le_one hM).mpr (hbound _)
  let R := (M:ℂ) • correspondenceOperatorComplexHermiteMultiplier hn w hw
  have hc (f : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
      gaussianHermiteCoefficient hn (R f) pq=
        (((n*totalAntiDegree pq:ℕ):ℂ)-z)⁻¹*gaussianHermiteCoefficient hn f pq := by
    change gaussianHermiteCoefficient hn ((M:ℂ) • correspondenceOperatorComplexHermiteMultiplier hn w hw f) pq=_
    rw [gaussianHermiteCoefficient_eq_inner,inner_smul_right,← gaussianHermiteCoefficient_eq_inner]
    change (M:ℂ)*gaussianHermiteCoefficient hn (correspondenceOperatorComplexHermiteMultiplierValue hn w hw f) pq=_
    rw [correspondenceOperatorComplexHermiteMultiplier_coefficient]
    dsimp [w]
    have hm : (M:ℂ)≠0 := by exact_mod_cast hM.ne'
    field_simp
  refine ⟨R,?_,?_⟩
  · intro f
    rw [correspondenceOperatorNumber_graph]
    intro pq
    have he : (((n*totalAntiDegree pq:ℕ):ℂ)-z)≠0 := sub_ne_zero.mpr (Ne.symm (hz _))
    simp only [gaussianHermiteCoefficient_eq_inner,inner_add_right,inner_smul_right]
    simp only [← gaussianHermiteCoefficient_eq_inner]
    rw [hc]
    field_simp <;> ring
  · intro u v huv
    rw [correspondenceOperatorNumber_graph] at huv
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    rw [hc]
    have he : (((n*totalAntiDegree pq:ℕ):ℂ)-z)≠0 := sub_ne_zero.mpr (Ne.symm (hz _))
    simp only [gaussianHermiteCoefficient_eq_inner,inner_sub_right,inner_smul_right]
    simp only [← gaussianHermiteCoefficient_eq_inner]
    rw [huv pq]
    field_simp <;> ring

/-- Every n-times-integer level is a literal eigenvalue of the actual operator. -/
theorem correspondenceOperatorNumber_level_eigenvector (n : ℕ) (hn : 0<n) (k : ℕ) :
    ∃u : Lp ℂ 2 (complexGaussianMeasure n),u≠0 ∧
      (u,((n*k:ℕ):ℂ) • u)∈(correspondenceOperatorNumber n hn).graph := by
  classical
  let j : Fin n := ⟨0,hn⟩
  let pq : HermiteMultiIndex n := (0,Pi.single j k)
  have hd : totalAntiDegree pq=k := by
    simp [pq,totalAntiDegree,Finset.sum_pi_single]
  refine ⟨(gaussianHermiteHilbertBasis n hn) pq,
    (gaussianHermiteHilbertBasis n hn).orthonormal.ne_zero pq,?_⟩
  rw [correspondenceOperatorNumber_graph]
  intro ab
  have hc : gaussianHermiteCoefficient hn ((gaussianHermiteHilbertBasis n hn) pq) ab=
      if ab=pq then 1 else 0 := by
    change (gaussianHermiteHilbertBasis n hn).repr ((gaussianHermiteHilbertBasis n hn) pq) ab=_
    rw [HilbertBasis.repr_self,lp.single_apply]
    simp [Pi.single_apply]
  rw [gaussianHermiteCoefficient_eq_inner,inner_smul_right,← gaussianHermiteCoefficient_eq_inner,hc]
  by_cases h : ab=pq
  · subst ab
    simp [hd]
  · simp [h]

/-- Exact complex spectrum of the maximal differential number operator,
expressed by failure of a bounded two-sided inverse on its literal graph. -/
theorem correspondenceOperatorNumber_spectrum_iff (n : ℕ) (hn : 0<n) (z : ℂ) :
    ¬correspondenceOperatorNumberHasResolvent n hn z ↔ ∃k : ℕ,z=((n*k:ℕ):ℂ) := by
  constructor
  · intro hz
    by_contra h
    push_neg at h
    exact hz (correspondenceOperatorNumber_resolvent_outside n hn z h)
  · rintro ⟨k,rfl⟩ ⟨R,hR,hL⟩
    obtain ⟨u,hu,hg⟩ := correspondenceOperatorNumber_level_eigenvector n hn k
    have he := hL u (((n*k:ℕ):ℂ) • u) hg
    simp only [sub_self,map_zero] at he
    exact hu he.symm
#print axioms correspondenceOperatorNumber_level_eigenvector
#print axioms correspondenceOperatorNumber_spectrum_iff
#print axioms correspondenceOperatorNumber_inverse_weights_bounded
#print axioms correspondenceOperatorNumber_resolvent_outside
end
end GinibrePoincare
