module

public import GinibrePoincare.Analysis.GinibreFullSemigroup
public import GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute

@[expose] public section

/-! # Closed real invariant subspaces of the full spectral evolution -/
open Filter
open scoped NNReal Topology ContinuousFunctionalCalculus
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Real spectral calculus on a complex Hilbert space, bundled before instantiation. -/
def resolventRealCfc (R : H →L[ℂ] H) (f : ℝ → ℝ) : H →L[ℂ] H := cfc f R

/-- Real continuous functional calculus preserves every closed real invariant subspace. -/
theorem cfc_real_preserves_closed_submodule (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (M : Submodule ℝ H) (hM : IsClosed (M : Set H))
    (hRM : ∀ x ∈ M, R x ∈ M) (f : ℝ → ℝ) (hf : ContinuousOn f (spectrum ℝ R)) :
    ∀ x ∈ M, cfc f R x ∈ M := by
  have hall : ∀ g : C(spectrum ℝ R, ℝ), ∀ x ∈ M, cfcHom hR g x ∈ M := by
    intro g
    induction g using ContinuousMap.induction_on_of_compact with
    | const r =>
      intro x hx
      change (cfcHom hR (algebraMap ℝ C(spectrum ℝ R, ℝ) r)) x ∈ M
      rw [AlgHomClass.commutes]
      exact M.smul_mem r hx
    | id =>
      rw [cfcHom_id hR]
      exact hRM
    | star_id =>
      rw [map_star, cfcHom_id hR, hR.star_eq]
      exact hRM
    | add g h hg hh =>
      intro x hx
      rw [map_add, add_apply]
      exact M.add_mem (hg x hx) (hh x hx)
    | mul g h hg hh =>
      intro x hx
      rw [map_mul]
      exact hg _ (hh x hx)
    | frequently g hg =>
      intro x hx
      apply hM.mem_of_frequently_of_tendsto (hg.mono (fun h hh => hh x hx))
      exact ((ContinuousLinearMap.apply ℂ H x).continuous.tendsto _).comp
        ((cfcHom_continuous hR).tendsto g)
  rw [cfc_apply f R hR hf]
  exact hall _

/-- Every real continuous spectral multiplier preserves actual real observables. -/
theorem ginibreFullCfc_im_zero (n : ℕ) (hn : 0 < n) (f : ℝ → ℝ)
    (hf : ContinuousOn f (spectrum ℝ (ginibreFullComplexResolvent n hn)))
    (u : ginibreSymmetricL2 n) (hu : ginibreFullSymmetricIm n u = 0) :
    ginibreFullSymmetricIm n (resolventRealCfc (ginibreFullComplexResolvent n hn) f u) = 0 := by
  let M := (ginibreFullSymmetricIm n).ker
  have hm : IsClosed (M : Set (ginibreSymmetricL2 n)) :=
    (ginibreFullSymmetricIm n).isClosed_ker
  have hr : ∀ x ∈ M, ginibreFullComplexResolvent n hn x ∈ M := by
    intro x hx
    change ginibreFullSymmetricIm n (ginibreFullComplexResolvent n hn x) = 0
    rw [ginibreFullComplexResolvent_im, show ginibreFullSymmetricIm n x = 0 from hx, map_zero]
  exact cfc_real_preserves_closed_submodule _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    M hm hr f hf u hu

/-- The full diffusion preserves actual real-valued observables. -/
theorem ginibreFullEvolution_im_zero (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : ginibreSymmetricL2 n) (hu : ginibreFullSymmetricIm n u = 0) :
    ginibreFullSymmetricIm n (ginibreFullEvolution n hn t u) = 0 :=
  ginibreFullCfc_im_zero n hn _ (resolventEvolutionMultiplier_continuous _).continuousOn u hu

/-- The real full diffusion, on the actual symmetric real weighted L² space. -/
def ginibreFullRealEvolution (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    ginibreFullSymmetricValues n →L[ℝ] ginibreFullSymmetricValues n :=
  (ginibreFullSymmetricRe n).comp
    (((ginibreFullEvolution n hn t).restrictScalars ℝ).comp (ginibreFullSymmetricOfReal n))

/-- Complex evolution of an actual real input agrees with its real restriction. -/
theorem ginibreFullEvolution_ofReal (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (u : ginibreFullSymmetricValues n) :
    ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n u) =
      ginibreFullSymmetricOfReal n (ginibreFullRealEvolution n hn t u) := by
  apply Subtype.ext
  rw [← ginibreFullComplex_decomposition n
    (ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n u)).val]
  have hz := ginibreFullEvolution_im_zero n hn t (ginibreFullSymmetricOfReal n u)
    (ginibreFullSymmetricIm_ofReal n u)
  have hzv : ginibreFullComplexIm n
      (ginibreFullEvolution n hn t (ginibreFullSymmetricOfReal n u)).val = 0 :=
    congrArg Subtype.val hz
  rw [hzv, map_zero, smul_zero, add_zero]
  rfl

end
end GinibrePoincare
