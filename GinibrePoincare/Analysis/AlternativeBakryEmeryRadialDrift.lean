module

public import GinibrePoincare.Analysis.NonQuadraticRadialBochner

@[expose] public section

/-! # Actual dissipative drift of the positive-radius diffusion
This is a local flow ingredient, rather than an entropy or LSI endpoint.
-/

open Set
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The literal unit-diffusion Langevin drift for a Kostlan radius. -/
def bakryEmeryRadialDrift (n k : ℕ) (V : Potential) (r : ℝ) : ℝ :=
  -deriv (radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))) r

/-- The drift contracts at the exact curvature scale `nρ`. -/
theorem bakryEmeryRadialDrift_deriv_le (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hc : IsRhoConvexPotential ρ V)
    (r : ℝ) (hr : 0 < r) :
    deriv (bakryEmeryRadialDrift n k V) r ≤ -(n : ℝ) * ρ := by
  have h := rhoConvexPotential_radial_curvature n k hk ρ hV hc r hr
  unfold bakryEmeryRadialDrift
  rw [deriv.fun_neg]
  linarith

/-- The shifted radial drift is decreasing on its actual positive domain. -/
theorem bakryEmeryRadialDrift_shift_antitone (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hc : IsRhoConvexPotential ρ V) :
    AntitoneOn (fun r => bakryEmeryRadialDrift n k V r + (n : ℝ) * ρ * r) (Ioi 0) := by
  let W := radialEffectivePotential n k (fun t : ℝ => V (t : ℂ))
  have hdW (r : ℝ) (hr : 0 < r) : ContDiffAt ℝ 1 (deriv W) r := by
    exact (show ContDiffAt ℝ (1 + 1) W r from
      contDiffAt_radialEffectivePotential n k hV r hr).derivWithin (by norm_num)
  have hd (r : ℝ) (hr : 0 < r) :
      HasDerivAt (fun t => bakryEmeryRadialDrift n k V t + (n : ℝ) * ρ * t)
        (deriv (bakryEmeryRadialDrift n k V) r + (n : ℝ) * ρ) r := by
    have hb : DifferentiableAt ℝ (bakryEmeryRadialDrift n k V) r :=
      (hdW r hr).differentiableAt (by norm_num) |>.neg
    convert hb.hasDerivAt.add
      ((hasDerivAt_id r).const_mul ((n : ℝ) * ρ)) using 1 <;> simp [id_eq]
    funext t
    rfl
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro r hr
    exact (hd r hr).continuousAt.continuousWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ioi, mem_Ioi] using hr
    exact (hd r hr').differentiableAt.differentiableWithinAt
  · intro r hr
    have hr' : 0 < r := by simpa only [interior_Ioi, mem_Ioi] using hr
    rw [(hd r hr').deriv]
    linarith [bakryEmeryRadialDrift_deriv_le n k hk ρ hV hc r hr']

/-- Dissipativity for arbitrary two positive radii, the estimate needed for
synchronous coupling of the actual diffusion. -/
theorem bakryEmeryRadialDrift_dissipative (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hc : IsRhoConvexPotential ρ V)
    (r s : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (bakryEmeryRadialDrift n k V r - bakryEmeryRadialDrift n k V s) * (r - s) ≤
      -((n : ℝ) * ρ) * (r - s) ^ 2 := by
  have hm := bakryEmeryRadialDrift_shift_antitone n k hk ρ hV hc
  rcases le_total r s with h | h
  · have hmono := hm hr hs h
    have hh := mul_le_mul_of_nonpos_right hmono (sub_nonpos.mpr h)
    nlinarith
  · have hmono := hm hs hr h
    have hh := mul_le_mul_of_nonneg_right hmono (sub_nonneg.mpr h)
    nlinarith

/-- Synchronous positive-radius trajectories contract at the exact rate `nρ`.
Only the derivative of their difference is required, so continuous common
Brownian forcing cancels before this deterministic argument. -/
theorem bakryEmeryRadial_synchronous_contraction (n k : ℕ) (hk : 1 ≤ k) (ρ : ℝ)
    {V : Potential} (hV : ContDiff ℝ 2 V) (hc : IsRhoConvexPotential ρ V)
    (X Y : ℝ → ℝ) (hX : ContinuousOn X (Ici 0)) (hY : ContinuousOn Y (Ici 0))
    (hXp : ∀ t, 0 ≤ t → 0 < X t) (hYp : ∀ t, 0 ≤ t → 0 < Y t)
    (heq : ∀ t, 0 < t → HasDerivAt (fun s => X s - Y s)
      (bakryEmeryRadialDrift n k V (X t) - bakryEmeryRadialDrift n k V (Y t)) t)
    (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (2 * ((n : ℝ) * ρ) * t) * (X t - Y t) ^ 2 ≤ (X 0 - Y 0) ^ 2 := by
  let κ := (n : ℝ) * ρ
  let D : ℝ → ℝ := fun s => Real.exp (2 * κ * s) * (X s - Y s) ^ 2
  have hDc : ContinuousOn D (Ici 0) := by
    exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
      ((hX.sub hY).pow 2)
  have hd (s : ℝ) (hs : 0 < s) : HasDerivAt D
      (2 * Real.exp (2 * κ * s) *
        (κ * (X s - Y s) ^ 2 +
          (bakryEmeryRadialDrift n k V (X s) - bakryEmeryRadialDrift n k V (Y s)) *
            (X s - Y s))) s := by
    have he := (((hasDerivAt_id s).const_mul (2 * κ)).exp).mul ((heq s hs).pow 2)
    convert he using 1 <;> dsimp [D] <;> try ring
    funext x
    simp only [Pi.mul_apply, Pi.pow_apply]
    ring
  have hmono : AntitoneOn D (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0) hDc
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
      exact (hd s hs').differentiableAt.differentiableWithinAt
    · intro s hs
      have hs' : 0 < s := by simpa only [interior_Ici, mem_Ioi] using hs
      rw [(hd s hs').deriv]
      have hcoup := bakryEmeryRadialDrift_dissipative n k hk ρ hV hc
        (X s) (Y s) (hXp s hs'.le) (hYp s hs'.le)
      have hnon : κ * (X s - Y s) ^ 2 +
          (bakryEmeryRadialDrift n k V (X s) - bakryEmeryRadialDrift n k V (Y s)) *
            (X s - Y s) ≤ 0 := by dsimp [κ]; linarith
      exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hnon
  have hb := hmono (show (0 : ℝ) ∈ Ici 0 by simp) ht ht
  simpa [D, κ] using hb

#print axioms bakryEmeryRadial_synchronous_contraction

#print axioms bakryEmeryRadialDrift_deriv_le
#print axioms bakryEmeryRadialDrift_shift_antitone
#print axioms bakryEmeryRadialDrift_dissipative

end
end GinibrePoincare
