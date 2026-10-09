module

public import GinibrePoincare.Analysis.GinibreFullSemigroupDynamics
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus

@[expose] public section

/-! Hilbert-space orbit uniqueness from actual differential dissipation.
This is used after identification of the full resolvent domain. -/
open Set
namespace GinibrePoincare

theorem realHilbert_orbit_unique_of_dissipative_derivative {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x y vx vy : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hx : ContinuousOn x (Icc 0 T)) (hy : ContinuousOn y (Icc 0 T))
    (hdx : ∀ s ∈ Ioo 0 T, HasDerivAt x (vx s) s)
    (hdy : ∀ s ∈ Ioo 0 T, HasDerivAt y (vy s) s)
    (hdiss : ∀ s ∈ Ioo 0 T, inner ℝ (x s-y s) (vx s-vy s) ≤ 0)
    (hinit : x 0=y 0) : ∀ s ∈ Icc 0 T, x s=y s := by
  let F := fun s => ‖x s-y s‖^2
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) : HasDerivAt F
      (2*inner ℝ (x s-y s) (vx s-vy s)) s := ((hdx s hs).sub (hdy s hs)).norm_sq
  have hdiff : DifferentiableOn ℝ F (interior (Icc 0 T)) := by
    rw [interior_Icc]
    exact fun s hs => (hd s hs).differentiableAt.differentiableWithinAt
  have hnonpos : ∀ s ∈ interior (Icc 0 T), deriv F s ≤ 0 := by
    rw [interior_Icc]
    intro s hs
    rw [(hd s hs).deriv]
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) (hdiss s hs)
  have hanti : AntitoneOn F (Icc 0 T) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 T) ((hx.sub hy).norm.pow 2) hdiff hnonpos
  intro s hs
  have hh := hanti ⟨le_rfl, hT⟩ hs hs.1
  have hz : F 0=0 := by simp [F, hinit]
  rw [hz] at hh
  have hn : ‖x s-y s‖=0 := by dsimp [F] at hh; nlinarith [norm_nonneg (x s-y s)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

#print axioms realHilbert_orbit_unique_of_dissipative_derivative
end GinibrePoincare
