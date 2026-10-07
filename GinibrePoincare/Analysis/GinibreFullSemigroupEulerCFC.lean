module

public import GinibrePoincare.Analysis.GinibreFullSemigroupEulerMultiplier
public import GinibrePoincare.Analysis.GinibreFullSemigroupRealInvariant
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

@[expose] public section

/-! # Actual backward Euler operators and norm convergence -/
open Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The backward Euler operator of the resolvent-defined generator. -/
def resolventBackwardEuler (R : H →L[ℂ] H) (c : ℝ) : H →L[ℂ] H :=
  cfc (backwardEulerResolventMultiplier c) R

def resolventBackwardEulerImage (R : H →L[ℂ] H) (c : ℝ) : H →L[ℂ] H :=
  cfc (fun r => (backwardEulerResolventMultiplier c r - 1) / c) R

/-- Every Euler output belongs to the actual generator graph. -/
theorem resolventBackwardEuler_graph (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hc : 0 < c) (x : H) :
    R (resolventBackwardEuler R c x - resolventBackwardEulerImage R c x) =
      resolventBackwardEuler R c x := by
  let f := backwardEulerResolventMultiplier c
  let g := fun r => (f r - 1) / c
  have hf : ContinuousOn f (spectrum ℝ R) :=
    (backwardEulerResolventMultiplier_continuousOn hc).mono (fun r hr => hSpec r hr)
  have hg : ContinuousOn g (spectrum ℝ R) := (hf.sub continuousOn_const).div_const c
  have hi : cfc (fun r : ℝ => r * (f r - g r)) R = cfc f R := by
    apply cfc_congr
    intro r hr
    exact backwardEulerResolventMultiplier_graph_identity hc (hSpec r hr)
  rw [cfc_mul (fun r : ℝ => r) (fun r => f r - g r) R continuousOn_id (hf.sub hg), cfc_id' ℝ R hR,
    cfc_sub f g R hf hg] at hi
  exact congrArg (fun A : H →L[ℂ] H => A x) hi

/-- The backward Euler equation holds without any domain hypothesis on the input. -/
theorem resolventBackwardEuler_equation (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (c : ℝ) (hc : 0 < c) (x : H) :
    resolventBackwardEuler R c x - c • resolventBackwardEulerImage R c x = x := by
  let f := backwardEulerResolventMultiplier c
  let g := fun r => (f r - 1) / c
  have hf : ContinuousOn f (spectrum ℝ R) :=
    (backwardEulerResolventMultiplier_continuousOn hc).mono (fun r hr => hSpec r hr)
  have hg : ContinuousOn g (spectrum ℝ R) := (hf.sub continuousOn_const).div_const c
  have hi : cfc (fun r : ℝ => f r - c * g r) R = 1 := by
    rw [show cfc (fun r : ℝ => f r - c * g r) R = cfc (fun _ : ℝ => 1) R from
      cfc_congr (fun r _ => by dsimp [g]; field_simp; ring)]
    exact cfc_one ℝ R hR
  rw [cfc_sub f (fun r => c * g r) R hf (continuousOn_const.mul hg),
    cfc_const_mul c g R hg] at hi
  exact congrArg (fun A : H →L[ℂ] H => A x) hi

/-- Dyadic backward Euler powers converge in operator norm at every positive time. -/
theorem resolventBackwardEuler_pow_tendsto (R : H →L[ℂ] H) (hR : IsSelfAdjoint R)
    (hSpec : ∀ r ∈ spectrum ℝ R, r ∈ Set.Icc (0 : ℝ) 1)
    (t : ℝ) (ht : 0 < t) :
    Tendsto (fun j : ℕ => (resolventBackwardEuler R (t / (2 ^ j : ℕ))) ^ (2 ^ j : ℕ))
      atTop (𝓝 (cfc (resolventEvolutionMultiplier t) R)) := by
  have h := tendsto_cfc_fun (a := R)
    ((resolventEulerMultiplier_tendstoUniformlyOn ht).mono (fun r hr => hSpec r hr))
    (Eventually.of_forall fun j =>
      (resolventEulerMultiplier_continuousOn ht j).mono (fun r hr => hSpec r hr))
  convert h using 1
  funext j
  exact (cfc_pow (backwardEulerResolventMultiplier (t / (2 ^ j : ℕ))) (2 ^ j : ℕ) R
    ((backwardEulerResolventMultiplier_continuousOn (by positivity)).mono
      (fun r hr => hSpec r hr)) hR).symm

end
end GinibrePoincare
