module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-! # The entropy/Fisher differential implication

This is the calculus step of Bakry–Émery, stated as a reduction. The entropy
and Fisher dissipation equations and their equilibrium limits must still be
proved for the concrete diffusion before this yields a concrete LSI.
-/

open Set Filter
open scoped Topology
namespace GinibrePoincare

/-- The entropy/Fisher dissipation argument, with exact coefficient `1/(2κ)`.
The assumptions are scalar flow facts; this theorem does not manufacture a
diffusion satisfying them. -/
theorem bakryEmery_entropyFlow_bound (E I : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ)
    (hEc : ContinuousOn E (Ici 0)) (hIc : ContinuousOn I (Ici 0))
    (hE : ∀ t, 0 < t → HasDerivAt E (-I t) t)
    (hI : ∀ t, 0 < t → DifferentiableAt ℝ I t)
    (hcurv : ∀ t, 0 < t → deriv I t ≤ -2 * κ * I t)
    (hEinf : Tendsto E atTop (𝓝 0)) (hIinf : Tendsto I atTop (𝓝 0)) :
    ∀ t, 0 ≤ t → E t ≤ I t / (2 * κ) := by
  let D : ℝ → ℝ := fun t => E t - I t / (2 * κ)
  have hd (t : ℝ) (ht : 0 < t) :
      HasDerivAt D (-I t - deriv I t / (2 * κ)) t :=
    (hE t ht).sub ((hI t ht).hasDerivAt.div_const (2 * κ))
  have hmono : MonotoneOn D (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (hEc.sub (hIc.div_const _))
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      exact (hd t ht').differentiableAt.differentiableWithinAt
    · intro t ht
      have ht' : 0 < t := by simpa only [interior_Ici, mem_Ioi] using ht
      change 0 ≤ deriv D t
      rw [(hd t ht').deriv]
      have heq : (-2 * κ * I t) / (2 * κ) = -I t := by field_simp
      have hle : deriv I t / (2 * κ) ≤ -I t := by
        exact (div_le_div_of_nonneg_right (hcurv t ht') (by positivity)).trans_eq heq
      linarith
  have hlim : Tendsto D atTop (𝓝 0) := by
    simpa [D] using hEinf.sub (hIinf.div_const (2 * κ))
  intro t ht
  have hle : D t ≤ 0 := by
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop t] with s hs
    exact hmono ht (ht.trans hs) hs
  exact sub_nonpos.mp hle

#print axioms bakryEmery_entropyFlow_bound

end GinibrePoincare
