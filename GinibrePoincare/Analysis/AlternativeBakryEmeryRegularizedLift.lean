module

public import GinibrePoincare.Analysis.AlternativeBakryEmeryConvexLift
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! # Smooth strongly convex regularizations of the radial Euclidean lift

The positive extra coordinate removes the nonsmoothness of the radius at the
origin. The strong-convexity parameter remains exactly `nρ`.
-/
open Set Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def bakryEmeryRegularizedLiftPotential {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (V : Potential) (ε : ℝ) (x : E) : ℝ :=
  (n : ℝ) * V (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) : ℂ)

theorem bakryEmeryRegularizedLift_contDiff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (n : ℕ) (V : Potential) (ε : ℝ)
    (hV : ContDiff ℝ 2 V) (hε : 0 < ε) :
    ContDiff ℝ 2 (bakryEmeryRegularizedLiftPotential (E := E) n V ε) := by
  have hq : ContDiff ℝ 2 (fun x : E => ‖x‖ ^ 2 + ε ^ 2) :=
    (contDiff_norm_sq ℝ).add contDiff_const
  have hpos (x : E) : ‖x‖ ^ 2 + ε ^ 2 ≠ 0 := by
    nlinarith [sq_nonneg ‖x‖, sq_pos_of_pos hε]
  exact contDiff_const.mul (hV.comp (Complex.ofRealCLM.contDiff.comp (hq.sqrt hpos)))

def bakryEmeryExtraCoordinate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ε : ℝ) : E →ᵃ[ℝ] WithLp 2 (E × ℝ) :=
  ((WithLp.linearEquiv 2 ℝ (E × ℝ)).symm.toLinearMap.toAffineMap).comp
    ((AffineMap.id ℝ E).prod (AffineMap.const ℝ E ε))

theorem bakryEmeryExtraCoordinate_norm_sq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ε : ℝ) (x : E) :
    ‖bakryEmeryExtraCoordinate ε x‖ ^ 2 = ‖x‖ ^ 2 + ε ^ 2 := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  simp [bakryEmeryExtraCoordinate, Real.norm_eq_abs, sq_abs]

theorem bakryEmeryExtraCoordinate_norm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (ε : ℝ) (x : E) :
    ‖bakryEmeryExtraCoordinate ε x‖ = Real.sqrt (‖x‖ ^ 2 + ε ^ 2) := by
  rw [← bakryEmeryExtraCoordinate_norm_sq ε x, Real.sqrt_sq (norm_nonneg _)]

/-- Global strong convexity is preserved with no loss of the exact `nρ`
constant when the confinement is regularized by an extra coordinate. -/
theorem bakryEmeryRegularizedLift_strongConvex {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (ρ ε : ℝ) {V : Potential}
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ (univ : Set E) (fun x =>
      bakryEmeryRegularizedLiftPotential n V ε x - ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) := by
  have h := (bakryEmeryEuclideanLift_strongConvex
    (E := WithLp 2 (E × ℝ)) n ρ hrot hc).comp_affineMap
      (bakryEmeryExtraCoordinate (E := E) ε)
  have h' := h.add_const (((n : ℝ) * ρ) / 2 * ε ^ 2)
  convert h' using 1
  · simp
  · funext x
    change (n : ℝ) * V (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) : ℂ) - ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2 =
      ((n : ℝ) * V (‖bakryEmeryExtraCoordinate ε x‖ : ℂ) -
        ((n : ℝ) * ρ) / 2 * ‖bakryEmeryExtraCoordinate ε x‖ ^ 2) +
        ((n : ℝ) * ρ) / 2 * ε ^ 2
    rw [bakryEmeryExtraCoordinate_norm_sq, bakryEmeryExtraCoordinate_norm]
    ring

/-- The regularized potentials converge pointwise to the original radial lift. -/
theorem bakryEmeryRegularizedLift_tendsto {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (V : Potential) (hV : Continuous V) (x : E) :
    Tendsto (fun ε : ℝ => bakryEmeryRegularizedLiftPotential n V ε x) (𝓝 0)
      (𝓝 (bakryEmeryEuclideanLiftPotential n V x)) := by
  have hq : Tendsto (fun ε : ℝ => ‖x‖ ^ 2 + ε ^ 2) (𝓝 0) (𝓝 (‖x‖ ^ 2)) := by
    simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℝ => ‖x‖ ^ 2) (𝓝 0) (𝓝 (‖x‖ ^ 2))).add
      ((tendsto_id : Tendsto (fun ε : ℝ => ε) (𝓝 0) (𝓝 0)).pow 2))
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hq
  have hC := Complex.continuous_ofReal.continuousAt.tendsto.comp hs
  have hh := hV.continuousAt.tendsto.comp hC
  simpa [bakryEmeryRegularizedLiftPotential, bakryEmeryEuclideanLiftPotential,
    Real.sqrt_sq (norm_nonneg x)] using hh.const_mul (n : ℝ)

/-- Uniform quadratic confinement, including the positive extra coordinate. -/
theorem bakryEmeryRegularizedLift_quadratic_lower_bound {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (ρ ε : ℝ) {V : Potential} (hrot : IsRotationalPotential V)
    (hc : IsRhoConvexPotential ρ V) (x : E) :
    ((n : ℝ) * ρ) / 2 * (‖x‖ ^ 2 + ε ^ 2) + (n : ℝ) * V 0 ≤
      bakryEmeryRegularizedLiftPotential n V ε x := by
  have h := rhoConvexPotential_quadratic_lower_bound ρ hrot hc
    (Real.sqrt (‖x‖ ^ 2 + ε ^ 2) : ℂ)
  rw [Complex.normSq_ofReal, Real.mul_self_sqrt (by positivity)] at h
  have hh := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  dsimp [bakryEmeryRegularizedLiftPotential]
  convert hh using 1 <;> ring

/-- A single Gaussian majorant dominates every positive regularization. -/
theorem bakryEmeryRegularizedLift_density_domination {E : Type*} [NormedAddCommGroup E]
    (n : ℕ) (ρ ε : ℝ) {V : Potential} (hρ : 0 ≤ ρ)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) (x : E) :
    Real.exp (-bakryEmeryRegularizedLiftPotential n V ε x) ≤
      Real.exp (-(n : ℝ) * V 0) * Real.exp (-((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := bakryEmeryRegularizedLift_quadratic_lower_bound n ρ ε hrot hc x
  have hpos : 0 ≤ ((n : ℝ) * ρ) / 2 * ε ^ 2 := by positivity
  nlinarith

end
end GinibrePoincare

#print axioms GinibrePoincare.bakryEmeryRegularizedLift_contDiff
#print axioms GinibrePoincare.bakryEmeryRegularizedLift_strongConvex
#print axioms GinibrePoincare.bakryEmeryRegularizedLift_tendsto

#print axioms GinibrePoincare.bakryEmeryExtraCoordinate_norm_sq
#print axioms GinibrePoincare.bakryEmeryExtraCoordinate_norm
#print axioms GinibrePoincare.bakryEmeryRegularizedLift_quadratic_lower_bound
#print axioms GinibrePoincare.bakryEmeryRegularizedLift_density_domination
