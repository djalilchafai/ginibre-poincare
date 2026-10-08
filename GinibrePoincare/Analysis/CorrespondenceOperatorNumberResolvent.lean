module
public import GinibrePoincare.Analysis.CorrespondenceOperatorHermiteMultiplier
@[expose] public section
open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
def correspondenceOperatorNumberResolventWeight (n : ℕ) (pq : HermiteMultiIndex n) : ℝ :=
  (1+(n*totalAntiDegree pq:ℕ))⁻¹
theorem correspondenceOperatorNumberResolventWeight_bound (n : ℕ) (pq : HermiteMultiIndex n) :
    |correspondenceOperatorNumberResolventWeight n pq|≤1 := by
  unfold correspondenceOperatorNumberResolventWeight
  rw [abs_of_nonneg (by positivity)]
  exact (inv_le_one₀ (by positivity)).mpr (le_add_of_nonneg_right (Nat.cast_nonneg _))
def correspondenceOperatorNumberResolvent (n : ℕ) (hn : 0<n) :
    Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n) :=
  correspondenceOperatorHermiteMultiplier hn (correspondenceOperatorNumberResolventWeight n)
    (correspondenceOperatorNumberResolventWeight_bound n)

theorem correspondenceOperatorNumberResolvent_coefficient (n : ℕ) (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (correspondenceOperatorNumberResolvent n hn u) pq=
      ((1+(n*totalAntiDegree pq:ℕ):ℂ)⁻¹)*gaussianHermiteCoefficient hn u pq := by
  change gaussianHermiteCoefficient hn (correspondenceOperatorHermiteMultiplierValue hn _ _ u) pq=_
  rw [correspondenceOperatorHermiteMultiplier_coefficient]
  simp [correspondenceOperatorNumberResolventWeight]

theorem correspondenceOperatorNumberResolvent_isSelfAdjoint (n : ℕ) (hn : 0<n) :
    IsSelfAdjoint (correspondenceOperatorNumberResolvent n hn) :=
  correspondenceOperatorHermiteMultiplier_isSelfAdjoint hn _ _

theorem correspondenceOperatorNumber_graph_iff_resolvent (n : ℕ) (hn : 0<n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) :
    (u,v)∈(correspondenceOperatorNumber n hn).graph ↔
      correspondenceOperatorNumberResolvent n hn (u+v)=u := by
  rw [correspondenceOperatorNumber_graph]
  constructor
  · intro huv
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    rw [correspondenceOperatorNumberResolvent_coefficient]
    have ha : gaussianHermiteCoefficient hn (u+v) pq=
      gaussianHermiteCoefficient hn u pq+gaussianHermiteCoefficient hn v pq := by
      simp only [gaussianHermiteCoefficient_eq_inner,inner_add_right]
    rw [ha,huv pq]
    have hk : (1+(n*totalAntiDegree pq:ℕ):ℂ)≠0 := by
      exact_mod_cast (show (1+(n*totalAntiDegree pq:ℕ):ℝ)≠0 by positivity)
    field_simp
  · intro huv pq
    have he := congrArg (fun x=>gaussianHermiteCoefficient hn x pq) huv
    rw [correspondenceOperatorNumberResolvent_coefficient] at he
    have ha : gaussianHermiteCoefficient hn (u+v) pq=
      gaussianHermiteCoefficient hn u pq+gaussianHermiteCoefficient hn v pq := by
      simp only [gaussianHermiteCoefficient_eq_inner,inner_add_right]
    rw [ha] at he
    have hk : (1+(n*totalAntiDegree pq:ℕ):ℂ)≠0 := by
      exact_mod_cast (show (1+(n*totalAntiDegree pq:ℕ):ℝ)≠0 by positivity)
    field_simp at he
    linear_combination he

theorem correspondenceOperatorNumberResolvent_injective (n : ℕ) (hn : 0<n) :
    Function.Injective (correspondenceOperatorNumberResolvent n hn) := by
  intro u v huv
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  have he := congrArg (fun x=>gaussianHermiteCoefficient hn x pq) huv
  rw [correspondenceOperatorNumberResolvent_coefficient,
    correspondenceOperatorNumberResolvent_coefficient] at he
  apply mul_left_cancel₀ _ he
  apply inv_ne_zero
  exact_mod_cast (show (1+(n*totalAntiDegree pq:ℕ):ℝ)≠0 by positivity)
#print axioms correspondenceOperatorNumber_graph_iff_resolvent
#print axioms correspondenceOperatorNumberResolvent_injective
end
end GinibrePoincare
