module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberDomain
public import GinibrePoincare.Analysis.GaussianEntireSpaceClosure
@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
/-- The maximal number kernel is precisely the literal holomorphic projection. -/
theorem correspondenceOperatorNumber_kernel_iff_zeroMode {n : ℕ} (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (u, 0)∈(correspondenceOperatorNumber n hn).graph ↔ gaussianHermiteMode hn 0 u=u := by
  rw [correspondenceOperatorNumber_graph]
  constructor
  · intro hu
    apply gaussianHermiteCoefficient_ext hn
    intro pq
    rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode]
    by_cases hd : totalAntiDegree pq=0
    · rw [if_pos hd]
    · rw [if_neg hd]
      have he := hu pq
      have hk : (n*totalAntiDegree pq : ℂ)≠0 := by
        exact_mod_cast Nat.mul_ne_zero hn.ne' hd
      have hz : gaussianHermiteCoefficient hn u pq=0 := by
        apply (mul_eq_zero.mp (show (n*totalAntiDegree pq : ℕ)*
          gaussianHermiteCoefficient hn u pq=0 by
          simpa [gaussianHermiteCoefficient_eq_inner] using he.symm)).resolve_left
        simpa only [Nat.cast_mul] using hk
      exact hz.symm
  · intro hu pq
    have he := congrArg (fun x=>gaussianHermiteCoefficient hn x pq) hu
    rw [gaussianHermiteCoefficient_eq_inner, inner_basis_gaussianHermiteMode] at he
    by_cases hd : totalAntiDegree pq=0
    · simp [hd, gaussianHermiteCoefficient_eq_inner]
    · simp only [if_neg hd] at he
      simp [he.symm, gaussianHermiteCoefficient_eq_inner]

/-- Every kernel vector, and only such a vector, has an actual entire
holomorphic representative on the full configuration space. -/
theorem correspondenceOperatorNumber_kernel_iff_entire {n : ℕ} (hn : 0<n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) :
    (u, 0)∈(correspondenceOperatorNumber n hn).graph ↔
      ∃f, IsGaussianEntireRepresentative u f := by
  rw [correspondenceOperatorNumber_kernel_iff_zeroMode]
  constructor
  · intro hu
    obtain ⟨f, hf⟩ := gaussianZeroMode_has_entire_representative hn u
    exact ⟨f, hu ▸ hf⟩
  · rintro ⟨f, hf⟩
    exact gaussianEntireRepresentative_zeroMode_eq hn u f hf
#print axioms correspondenceOperatorNumber_kernel_iff_zeroMode
#print axioms correspondenceOperatorNumber_kernel_iff_entire
end
end GinibrePoincare
