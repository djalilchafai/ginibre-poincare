module
public import GinibrePoincare.Analysis.CorrespondenceOperatorEvolution
public import GinibrePoincare.Analysis.GinibreFullSemigroupRealInvariant
@[expose] public section
namespace GinibrePoincare
noncomputable section
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
theorem correspondenceOperatorCfc_im_zero (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (correspondenceOperatorComplexResolvent n hn)))
    (u : GinibreFullComplexL2 n) (hu : ginibreFullComplexIm n u = 0) :
    ginibreFullComplexIm n (resolventRealCfc (correspondenceOperatorComplexResolvent n hn) f u) = 0 := by
  let M := (ginibreFullComplexIm n).ker
  have hm : IsClosed (M : Set (GinibreFullComplexL2 n)) :=
    (ginibreFullComplexIm n).isClosed_ker
  have hr : ∀ x ∈ M, correspondenceOperatorComplexResolvent n hn x ∈ M := by
    intro x hx
    change ginibreFullComplexIm n (correspondenceOperatorComplexResolvent n hn x) = 0
    rw [correspondenceOperatorComplexResolvent_im, show ginibreFullComplexIm n x = 0 from hx, map_zero]
  exact cfc_real_preserves_closed_submodule _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    M hm hr f hf u hu

/-- The full diffusion preserves actual real-valued observables. -/
theorem correspondenceOperatorEvolution_im_zero (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : GinibreFullComplexL2 n) (hu : ginibreFullComplexIm n u = 0) :
    ginibreFullComplexIm n (correspondenceOperatorEvolution n hn t u) = 0 :=
  correspondenceOperatorCfc_im_zero n hn _ (resolventEvolutionMultiplier_continuous _).continuousOn u hu

/-- The real full diffusion, on the actual symmetric real weighted L² space. -/
def correspondenceOperatorRealEvolution (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    GinibreFullValueL2 n →L[ℝ] GinibreFullValueL2 n :=
  (ginibreFullComplexRe n).comp
    (((correspondenceOperatorEvolution n hn t).restrictScalars ℝ).comp (ginibreFullComplexOfReal n))

/-- Complex evolution of an actual real input agrees with its real restriction. -/
theorem correspondenceOperatorEvolution_ofReal (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : GinibreFullValueL2 n) :
    correspondenceOperatorEvolution n hn t (ginibreFullComplexOfReal n u) =
      ginibreFullComplexOfReal n (correspondenceOperatorRealEvolution n hn t u) := by
  rw [← ginibreFullComplex_decomposition n
    (correspondenceOperatorEvolution n hn t (ginibreFullComplexOfReal n u))]
  have hz := correspondenceOperatorEvolution_im_zero n hn t (ginibreFullComplexOfReal n u)
    (ginibreFullComplexIm_ofReal n u)
  have hzv : ginibreFullComplexIm n
      (correspondenceOperatorEvolution n hn t (ginibreFullComplexOfReal n u)) = 0 :=
    hz
  rw [hzv, map_zero, smul_zero, add_zero]
  rfl

#print axioms correspondenceOperatorEvolution_ofReal
end
end GinibrePoincare
