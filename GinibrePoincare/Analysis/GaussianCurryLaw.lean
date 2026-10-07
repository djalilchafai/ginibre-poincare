module

public import GinibrePoincare.Analysis.GaussianPiCoordinates

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Linear currying of a finite family of real coordinates. -/
def gaussianCurryEquiv (I : Type*) (J : I → Type*) [Fintype I] [∀ i, Fintype (J i)] :
    ((Sigma J) → ℝ) ≃L[ℝ] (∀ i, J i → ℝ) where
  __ := LinearEquiv.piCurry ℝ (fun _ _ => ℝ)
  continuous_toFun := by
    change Continuous (fun x : Sigma J → ℝ => fun i j => x ⟨i, j⟩)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply (⟨i, j⟩ : Sigma J)
  continuous_invFun := by
    change Continuous (fun x : ∀ i, J i → ℝ => fun p : Sigma J => x p.1 p.2)
    apply continuous_pi
    intro p
    exact (continuous_apply p.2).comp (continuous_apply p.1)

/-- Finite Gaussian product measures commute with dependent currying. -/
theorem gaussianCurry_measurePreserving (I : Type*) (J : I → Type*)
    [Fintype I] [∀ i, Fintype (J i)] (v : ℝ≥0) :
    MeasurePreserving (gaussianCurryEquiv I J)
      (Measure.pi (fun _ : Sigma J => gaussianReal 0 v))
      (Measure.pi (fun i : I => Measure.pi (fun _ : J i => gaussianReal 0 v))) := by
  let e := MeasurableEquiv.piCurry (fun (i : I) (_ : J i) => ℝ)
  have hi : MeasurePreserving e.symm
      (Measure.pi (fun i : I => Measure.pi (fun _ : J i => gaussianReal 0 v)))
      (Measure.pi (fun _ : Sigma J => gaussianReal 0 v)) := by
    refine ⟨e.symm.measurable, ?_⟩
    apply Eq.symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs)]
    have hset : e.symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i : I => Set.univ.pi (fun j : J i => s ⟨i, j⟩)) := by
      ext x
      simp [e, Set.mem_pi, Sigma.forall, Sigma.uncurry]
    rw [hset, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun p : Sigma J => gaussianReal 0 v (s p))).symm
  exact MeasurePreserving.symm e.symm hi

end
end GinibrePoincare
