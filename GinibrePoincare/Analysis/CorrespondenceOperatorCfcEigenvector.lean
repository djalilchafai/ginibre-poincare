module
public import GinibrePoincare.Analysis.GinibreFullSemigroupRealInvariant
@[expose] public section
open Filter Set
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem correspondenceOperator_eigenvalue_mem_spectrum
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H→L[ℂ]H) (r : ℝ) (x : H) (hx0 : x≠0) (hx : R x=r • x) :
    r∈spectrum ℝ R := by
  rw [spectrum.mem_iff]
  rintro ⟨u,hu⟩
  have hz : (u : H→L[ℂ]H) x=0 := by
    rw [hu,Algebra.algebraMap_eq_smul_one]
    simp [hx]
  have he := congrArg (fun A : H→L[ℂ]H=>A x) u.inv_val
  have hxzero : x=0 := by
    change ((↑u⁻¹ : H→L[ℂ]H) ((u : H→L[ℂ]H) x))=x at he
    rw [hz,map_zero] at he
    exact he.symm
  exact hx0 hxzero
/-- Continuous spectral calculus acts on eigenvectors by literal evaluation;
no differentiability assumption on the spectral multiplier is needed. -/
theorem correspondenceOperator_cfc_eigenvector
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (R : H→L[ℂ]H) (hR : IsSelfAdjoint R) (r : ℝ) (hr : r∈spectrum ℝ R)
    (x : H) (hx : R x=r • x) (f : ℝ→ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    cfc f R x=f r • x := by
  have hall : ∀g : C(spectrum ℝ R,ℝ),cfcHom hR g x=g ⟨r,hr⟩ • x := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const a =>
      change (cfcHom hR (algebraMap ℝ C(spectrum ℝ R,ℝ) a)) x=a • x
      rw [AlgHomClass.commutes]
      rfl
    | id =>
      rw [cfcHom_id hR]
      exact hx
    | star_id =>
      rw [map_star,cfcHom_id hR,hR.star_eq]
      simpa using hx
    | add g h hg hh =>
      rw [map_add,ContinuousLinearMap.add_apply,hg,hh]
      exact (add_smul _ _ _).symm
    | mul g h hg hh =>
      rw [map_mul]
      change (cfcHom hR g) ((cfcHom hR h) x)=(g*h) ⟨r,hr⟩ • x
      rw [hh,ContinuousLinearMap.map_smul_of_tower,hg,smul_smul]
      simp [mul_comm]
    | frequently g hg =>
      have hEval : Continuous (fun h : C(spectrum ℝ R,ℝ)=>h ⟨r,hr⟩) := continuous_eval_const _
      have hclosed : IsClosed {h : C(spectrum ℝ R,ℝ) | cfcHom hR h x=h ⟨r,hr⟩ • x} :=
        isClosed_eq ((ContinuousLinearMap.apply ℂ H x).continuous.comp (cfcHom_continuous hR))
          (hEval.smul continuous_const)
      exact hclosed.mem_of_frequently_of_tendsto hg tendsto_id
  rw [cfc_apply f R hR hf]
  exact hall _
#print axioms correspondenceOperator_cfc_eigenvector
#print axioms correspondenceOperator_eigenvalue_mem_spectrum
end
end GinibrePoincare
