module

public import GinibrePoincare.Analysis.AlternativeBakryEmeryLangevinEnergy

@[expose] public section

/-! Actual derivative curvature of the strongly convex Langevin drift. -/
set_option backward.isDefEq.respectTransparency false
namespace GinibrePoincare
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Differentiating the actual dissipativity inequality gives the exact
linearized drift estimate, without assuming a flow or a Hessian bound. -/
theorem bakryEmeryLangevinDrift_derivative_curvature (W : E → ℝ) (κ : ℝ)
    (hW : ContDiff ℝ 2 W)
    (hc : ConvexOn ℝ univ (fun x => W x - κ/2*‖x‖^2)) (x v : E) :
    inner ℝ v ((fderiv ℝ (bakryEmeryLangevinDrift W) x) v) ≤ -κ*‖v‖^2 := by
  let b := bakryEmeryLangevinDrift W
  let F : ℝ → ℝ := fun t => inner ℝ v (b (x+t•v)) + κ*t*‖v‖^2
  have hdW : Differentiable ℝ W := hW.differentiable (by norm_num)
  have hmono : Antitone F := by
    intro s t hst
    rcases eq_or_lt_of_le hst with rfl | hst
    · exact le_rfl
    have he : x+t•v-(x+s•v) = (t-s)•v := by module
    have h := bakryEmeryLangevinDrift_dissipative W κ hc (x+t•v) (x+s•v)
      (hdW _) (hdW _)
    rw [he, inner_smul_left, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      inner_sub_right, conj_trivial] at h
    have hmul : (t-s)*F t ≤ (t-s)*F s := by
      dsimp [F,b]
      nlinarith only [h]
    exact (mul_le_mul_iff_right₀ (sub_pos.mpr hst)).mp hmul
  have hl : HasDerivAt (fun t : ℝ => x+t•v) v 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).smul_const v |>.const_add x
  have hb : DifferentiableAt ℝ b x :=
    (bakryEmeryLangevinDrift_contDiffAt W x hW.contDiffAt).differentiableAt (by norm_num)
  have hb' : HasFDerivAt b (fderiv ℝ b x) (x+(0:ℝ)•v) := by simpa using hb.hasFDerivAt
  have hdb := hb'.comp_hasDerivAt 0 hl
  have hinner := (innerSL ℝ v).hasFDerivAt.comp_hasDerivAt 0 hdb
  have hlinear := ((hasDerivAt_id (0:ℝ)).const_mul κ).mul_const (‖v‖^2)
  have hf := hinner.add hlinear
  have h := hf.nonpos_of_antitone hmono
  simp only [innerSL_apply_apply, b, mul_one] at h
  linarith

#print axioms bakryEmeryLangevinDrift_derivative_curvature
end GinibrePoincare
