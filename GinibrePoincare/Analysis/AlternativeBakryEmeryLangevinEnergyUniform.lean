module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinEnergy
@[expose] public section
open Set Metric
open scoped ContDiff NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Finite-time confinement with a fixed compact-noise drift bound, suitable
for removing a drift clipping whose radius is chosen before solving. -/
theorem bakryEmeryLangevin_driven_energy_bound_uniform
    (W : E → ℝ) (κ : ℝ) (hκ : 0 < κ) (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ/2*‖x‖^2))
    (N Y : ℝ → E) (T : ℝ) (hT : 0 ≤ T)
    (hY : ContinuousOn Y (Icc 0 T))
    (hEq : ∀ s ∈ Ioo 0 T, HasDerivAt Y (bakryEmeryLangevinDrift W (Y s+N s)) s)
    (C : ℝ) (hC : ∀ s ∈ Icc 0 T, ‖bakryEmeryLangevinDrift W (N s)‖ ≤ C) :
    ∀ t ∈ Icc 0 T, ‖Y t‖^2 ≤ ‖Y 0‖^2+(C^2/κ)*t := by
  have hd (s : ℝ) (hs : s ∈ Ioo 0 T) :
      HasDerivAt (fun t => ‖Y t‖ ^ 2)
        (2 * inner ℝ (Y s) (bakryEmeryLangevinDrift W (Y s + N s))) s :=
    (hEq s hs).norm_sq
  have hbound (s : ℝ) (hs : s ∈ Ioo 0 T) :
      2 * inner ℝ (Y s) (bakryEmeryLangevinDrift W (Y s + N s)) ≤ C ^ 2 / κ := by
    have hdis := bakryEmeryLangevinDrift_dissipative W κ hc (Y s + N s) (N s)
      ((hW.differentiable (by norm_num)) _) ((hW.differentiable (by norm_num)) _)
    simp only [add_sub_cancel_right, inner_sub_right] at hdis
    have hnoise : inner ℝ (Y s) (bakryEmeryLangevinDrift W (N s)) ≤ ‖Y s‖ * C :=
      (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hC s ⟨hs.1.le, hs.2.le⟩) (norm_nonneg _))
    have hcancel : κ * (C ^ 2 / κ) = C ^ 2 := mul_div_cancel₀ _ hκ.ne'
    have hfirst : 2 * inner ℝ (Y s) (bakryEmeryLangevinDrift W (Y s + N s)) ≤
        -2 * κ * ‖Y s‖ ^ 2 + 2 * ‖Y s‖ * C := by linarith
    have hscaled := mul_le_mul_of_nonneg_left hfirst hκ.le
    apply (mul_le_mul_iff_right₀ hκ).mp
    nlinarith [sq_nonneg (κ * ‖Y s‖ - C), sq_nonneg (‖Y s‖)]
  intro t ht
  have hfinal := (convex_Icc (0 : ℝ) T).image_sub_le_mul_sub_of_deriv_le
    (hY.norm.pow 2) (C := C ^ 2 / κ)
    (by
      intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt)
    (by
      intro s hs
      have hs' : s ∈ Ioo 0 T := by simpa only [interior_Icc] using hs
      change deriv (fun t => ‖Y t‖ ^ 2) s ≤ C ^ 2 / κ
      rw [(hd s hs').deriv]
      exact hbound s hs')
    0 ⟨le_rfl, hT⟩ t ht ht.1
  simp only [sub_zero, Pi.pow_apply] at hfinal
  linarith

#print axioms bakryEmeryLangevin_driven_energy_bound_uniform
end
end GinibrePoincare
