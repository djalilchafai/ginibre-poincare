module

public import GinibrePoincare.Analysis.NonQuadraticPiBergman

@[expose] public section

open MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- A finite product of commuting selfadjoint operators is selfadjoint. -/
theorem complexSuccessiveProjections_adjoint
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Ps : List (H →L[ℂ] H)) (ha : ∀ P ∈ Ps, P.adjoint = P)
    (hc : ∀ P ∈ Ps, ∀ Q ∈ Ps, P.comp Q = Q.comp P) :
    (complexSuccessiveProjections Ps).adjoint = complexSuccessiveProjections Ps := by
  induction Ps with
  | nil => exact ContinuousLinearMap.adjoint_id
  | cons P Ps ih =>
    have ht := ih (fun Q hQ => ha Q (List.mem_cons_of_mem _ hQ))
      (fun Q hQ R hR => hc Q (List.mem_cons_of_mem _ hQ) R (List.mem_cons_of_mem _ hR))
    change (P.comp (complexSuccessiveProjections Ps)).adjoint = P.comp (complexSuccessiveProjections Ps)
    rw [ContinuousLinearMap.adjoint_comp, ht, ha P (List.mem_cons_self ..)]
    exact (complexSuccessiveProjections_commutes Ps P
      (fun Q hQ => hc P (List.mem_cons_self ..) Q (List.mem_cons_of_mem _ hQ))).symm

/-- The actual whole-product nonquadratic Bergman projection is selfadjoint. -/
theorem planarPiBergmanProjection_adjoint {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) :
    (planarPiBergmanProjection (m := m) n V hV).adjoint = planarPiBergmanProjection n V hV := by
  apply complexSuccessiveProjections_adjoint
  · intro P hP
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
    exact planarPiBergmanCoordinate_adjoint n V hV i
  · intro P hP Q hQ
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hQ
    exact planarPiBergmanCoordinates_commute n V hV i j

#print axioms planarPiBergmanProjection_adjoint
end
end GinibrePoincare
