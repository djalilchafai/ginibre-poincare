module

public import GinibrePoincare.Analysis.NonQuadraticPiMultilinear
public import GinibrePoincare.Analysis.NonQuadraticMultilinearClosure
public import GinibrePoincare.Analysis.GeneralRadialProjectionMonomials
public import GinibrePoincare.Analysis.GeneralPotentialProjectionPermutation
public import GinibrePoincare.Analysis.NonQuadraticClosedSubmoduleIntegral

@[expose] public section

open MeasureTheory Set
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false

def planarPiWeightedMonomialVectors (d n : ℕ) (V : ℂ → ℝ) : Set (PlanarPiLebesgueL2 d) :=
  {F | ∃ u : Fin d → PlanarLebesgueL2, (∀ i, u i ∈ planarWeightedMonomialVectors n V) ∧
      l2PiProductVector (fun _ => (volume : Measure ℂ)) u = F}

theorem planarPiBergmanProjection_mem_weighted_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z) (F : PlanarPiLebesgueL2 (d+1)) :
    planarPiBergmanProjection n V hV F ∈
      (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  let K := (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure
  have hK : IsClosed (K : Set (PlanarPiLebesgueL2 (d+1))) :=
    (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).isClosed_topologicalClosure
  have hp (u : Fin (d+1) → PlanarLebesgueL2) :
      planarPiBergmanProjection n V hV (l2PiProductVector (fun _ => (volume : Measure ℂ)) u) ∈ K := by
    rw [planarPiBergmanProjection_pure]
    apply continuousMultilinear_mem_of_closed_factor_spans
      (l2PiProductContinuousMultilinear (fun _ : Fin (d+1) => (volume : Measure ℂ)))
      (fun _ => planarWeightedMonomialVectors n V) K hK
    · intro v hv
      exact (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).le_topologicalClosure
        (Submodule.subset_span ⟨v, hv, rfl⟩)
    · intro i
      exact planarBergmanKernel_le_weighted_monomial_closure n V hV hr
        (Submodule.starProjection_apply_mem (planarBergmanKernelClosed n V hV).toSubmodule (u i))
  letI : IsClosed (K : Set (PlanarPiLebesgueL2 (d+1))) := hK
  have he : K.mkQL.comp (planarPiBergmanProjection n V hV) = 0 := by
    apply l2PiOperators_ext_on_pure (d+1) (fun _ => (volume : Measure ℂ))
    intro u
    change K.mkQL (planarPiBergmanProjection n V hV (l2PiProductVector (fun _ => (volume : Measure ℂ)) u)) = 0
    exact (Submodule.Quotient.mk_eq_zero K).mpr (hp u)
  have hz := DFunLike.congr_fun he F
  change K.mkQL (planarPiBergmanProjection n V hV F) = 0 at hz
  exact (Submodule.Quotient.mk_eq_zero K).mp hz

theorem planarPiBergmanProjection_idempotent {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    (planarPiBergmanProjection (m := d) n V hV).comp (planarPiBergmanProjection n V hV) =
      planarPiBergmanProjection n V hV := by
  apply l2PiOperators_ext_on_pure (d+1) (fun _ => (volume : Measure ℂ))
  intro u
  simp only [ContinuousLinearMap.comp_apply, planarPiBergmanProjection_pure]
  congr 1
  funext i
  exact DFunLike.congr_fun
    (planarBergmanKernelClosed n V hV).toSubmodule.isIdempotentElem_starProjection (u i)

def planarPiBergmanJointKernel {d : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    Submodule ℂ (PlanarPiLebesgueL2 (d+1)) :=
  (ContinuousLinearMap.id ℂ _ - planarPiBergmanProjection n V hV).ker

theorem planarPiWeightedMonomialVector_fixed {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z)
    (F : PlanarPiLebesgueL2 (d+1)) (hF : F ∈ planarPiWeightedMonomialVectors (d+1) n V) :
    planarPiBergmanProjection n V hV F = F := by
  obtain ⟨u, hu, rfl⟩ := hF
  rw [planarPiBergmanProjection_pure]
  congr 1
  funext i
  apply Submodule.starProjection_eq_self_iff.mpr
  change u i ∈ planarBergmanKernel n V hV
  rw [planarBergmanKernel_eq_weighted_monomial_closure n V hV hr]
  exact (Submodule.span ℂ (planarWeightedMonomialVectors n V)).le_topologicalClosure
    (Submodule.subset_span (hu i))

theorem planarPiBergmanJointKernel_eq_weighted_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z) :
    planarPiBergmanJointKernel (d := d) n V hV =
      (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  apply le_antisymm
  · intro F hF
    have hf : planarPiBergmanProjection n V hV F = F := by
      change F - planarPiBergmanProjection n V hV F = 0 at hF
      exact (sub_eq_zero.mp hF).symm
    rw [← hf]
    exact planarPiBergmanProjection_mem_weighted_monomial_closure n V hV hr F
  · apply (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      intro F hF
      change F - planarPiBergmanProjection n V hV F = 0
      rw [planarPiWeightedMonomialVector_fixed n V hV hr F hF, sub_self]
    · exact ContinuousLinearMap.isClosed_ker _

theorem planarPiBergmanProjection_range_eq_weighted_monomial_closure {d : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (hr : ∀ a : ℂ, ‖a‖ = 1 → ∀ z, V (a*z) = V z) :
    (planarPiBergmanProjection (m := d) n V hV).range =
      (Submodule.span ℂ (planarPiWeightedMonomialVectors (d+1) n V)).topologicalClosure := by
  rw [← planarPiBergmanJointKernel_eq_weighted_monomial_closure n V hV hr]
  apply le_antisymm
  · rintro F ⟨G, rfl⟩
    change planarPiBergmanProjection n V hV G -
      planarPiBergmanProjection n V hV (planarPiBergmanProjection n V hV G) = 0
    rw [show planarPiBergmanProjection n V hV (planarPiBergmanProjection n V hV G) =
      planarPiBergmanProjection n V hV G from DFunLike.congr_fun (planarPiBergmanProjection_idempotent n V hV) G]
    exact sub_self _
  · intro F hF
    refine ⟨F, ?_⟩
    change F - planarPiBergmanProjection n V hV F = 0 at hF
    exact (sub_eq_zero.mp hF).symm

end
end GinibrePoincare
