module
public import GinibrePoincare.Analysis.CorrespondenceOperatorHermiteMultiplier
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberSpectralGraph
@[expose] public section
open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
def correspondenceOperatorNumberSpectralResolventWeight (n : ℕ) (f : ℝ→ℝ) (pq : HermiteMultiIndex n) : ℝ :=
  (1+f (n*totalAntiDegree pq:ℕ))⁻¹
theorem correspondenceOperatorNumberSpectralResolventWeight_bound (n : ℕ) (f : ℝ→ℝ) (hf : ∀x,0≤f x) (pq : HermiteMultiIndex n) :
    |correspondenceOperatorNumberSpectralResolventWeight n f pq|≤1 := by
  unfold correspondenceOperatorNumberSpectralResolventWeight
  have hp := hf (n*totalAntiDegree pq:ℕ)
  rw [abs_of_nonneg (by positivity)]
  exact (inv_le_one₀ (by positivity)).mpr (le_add_of_nonneg_right (hf _))
def correspondenceOperatorNumberSpectralResolvent (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) (hf : ∀x,0≤f x) :
    Lp ℂ 2 (complexGaussianMeasure n)→L[ℂ]Lp ℂ 2 (complexGaussianMeasure n) :=
  correspondenceOperatorHermiteMultiplier hn (correspondenceOperatorNumberSpectralResolventWeight n f)
    (correspondenceOperatorNumberSpectralResolventWeight_bound n f hf)

theorem correspondenceOperatorNumberSpectralResolvent_coefficient (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) (hf : ∀x,0≤f x)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (pq : HermiteMultiIndex n) :
    gaussianHermiteCoefficient hn (correspondenceOperatorNumberSpectralResolvent n hn f hf u) pq=
      ((1+(f (n*totalAntiDegree pq:ℕ):ℂ))⁻¹)*gaussianHermiteCoefficient hn u pq := by
  change gaussianHermiteCoefficient hn (correspondenceOperatorHermiteMultiplierValue hn _ _ u) pq=_
  rw [correspondenceOperatorHermiteMultiplier_coefficient]
  simp [correspondenceOperatorNumberSpectralResolventWeight]

theorem correspondenceOperatorNumberSpectralResolvent_isSelfAdjoint (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) (hf : ∀x,0≤f x) :
    IsSelfAdjoint (correspondenceOperatorNumberSpectralResolvent n hn f hf) :=
  correspondenceOperatorHermiteMultiplier_isSelfAdjoint hn _ _

theorem correspondenceOperatorNumberSpectral_graph_iff_resolvent (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) (hf : ∀x,0≤f x)
    (u v : Lp ℂ 2 (complexGaussianMeasure n)) :
    (u,v)∈(correspondenceOperatorNumberSpectral n hn f).graph ↔
      correspondenceOperatorNumberSpectralResolvent n hn f hf (u+v)=u := by
  rw [correspondenceOperatorNumberSpectral_graph]
  constructor
  · intro huv
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    rw [correspondenceOperatorNumberSpectralResolvent_coefficient]
    have ha : gaussianHermiteCoefficient hn (u+v) pq=
      gaussianHermiteCoefficient hn u pq+gaussianHermiteCoefficient hn v pq := by
      simp only [gaussianHermiteCoefficient_eq_inner,inner_add_right]
    rw [ha,huv pq]
    have hp := hf (n*totalAntiDegree pq:ℕ)
    have hk : (1+(f (n*totalAntiDegree pq:ℕ):ℂ))≠0 := by
      exact_mod_cast (show (1+f (n*totalAntiDegree pq:ℕ):ℝ)≠0 by positivity)
    field_simp
  · intro huv pq
    have he := congrArg (fun x=>gaussianHermiteCoefficient hn x pq) huv
    rw [correspondenceOperatorNumberSpectralResolvent_coefficient] at he
    have ha : gaussianHermiteCoefficient hn (u+v) pq=
      gaussianHermiteCoefficient hn u pq+gaussianHermiteCoefficient hn v pq := by
      simp only [gaussianHermiteCoefficient_eq_inner,inner_add_right]
    rw [ha] at he
    have hp := hf (n*totalAntiDegree pq:ℕ)
    have hk : (1+(f (n*totalAntiDegree pq:ℕ):ℂ))≠0 := by
      exact_mod_cast (show (1+f (n*totalAntiDegree pq:ℕ):ℝ)≠0 by positivity)
    field_simp at he
    linear_combination he

theorem correspondenceOperatorNumberSpectralResolvent_injective (n : ℕ) (hn : 0<n) (f : ℝ→ℝ) (hf : ∀x,0≤f x) :
    Function.Injective (correspondenceOperatorNumberSpectralResolvent n hn f hf) := by
  intro u v huv
  apply gaussianHermiteCoefficient_ext hn
  intro pq
  have he := congrArg (fun x=>gaussianHermiteCoefficient hn x pq) huv
  rw [correspondenceOperatorNumberSpectralResolvent_coefficient,
    correspondenceOperatorNumberSpectralResolvent_coefficient] at he
  apply mul_left_cancel₀ _ he
  apply inv_ne_zero
  have hp := hf (n*totalAntiDegree pq:ℕ)
  exact_mod_cast (show (1+f (n*totalAntiDegree pq:ℕ):ℝ)≠0 by positivity)
#print axioms correspondenceOperatorNumberSpectral_graph_iff_resolvent
#print axioms correspondenceOperatorNumberSpectralResolvent_injective
end
end GinibrePoincare
