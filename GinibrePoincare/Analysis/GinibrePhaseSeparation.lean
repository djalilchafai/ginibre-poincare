module

public import GinibrePoincare.Analysis.GinibrePhaseCoordinates
public import Mathlib.RingTheory.RootsOfUnity.Complex

@[expose] public section

/-! # Separating nonzero coordinates by independent unit phases

Every configuration whose coordinates are nonzero can be rotated independently
into a collision-free configuration, even when its original coordinates collide.
-/

open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000

/-- Fixed unit phases separate every configuration with at most one zero coordinate. -/
theorem exists_coordinatePhase_collisionFree_of_zero_injective (n : ℕ) (hn : 0 < n)
    (z : Configuration n) (hz : ∀ i j, z i = 0 → z j = 0 → i = j) :
    ∃ a : Fin n → ℂ, (∀ i, ‖a i‖ = 1) ∧ CollisionFree (coordinatePhase a z) := by
  classical
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / (n : ℂ))
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hζnorm : ‖ζ‖ = 1 := by
    simp [ζ, Complex.norm_exp, Complex.div_re]
  let b (i : Fin n) := ζ ^ (i : ℕ)
  have hb (i : Fin n) : ‖b i‖ = 1 := by simp [b, norm_pow, hζnorm]
  choose c hc he using (fun i : Fin n => Complex.exists_norm_mul_eq_self (z i))
  let a (i : Fin n) := b i * (c i)⁻¹
  have ha (i : Fin n) : ‖a i‖ = 1 := by simp [a, norm_mul, norm_inv, hb, hc]
  have hcne (i : Fin n) : c i ≠ 0 := by intro h; simpa [h] using hc i
  have hp (i : Fin n) : coordinatePhase a z i = (‖z i‖ : ℂ) * b i := by
    change (b i * (c i)⁻¹) * z i = _
    calc
      _ = (b i * (c i)⁻¹) * (c i * (‖z i‖ : ℂ)) :=
        congrArg (fun w => (b i * (c i)⁻¹) * w) (he i).symm
      _ = _ := by field_simp [hcne i]
  refine ⟨a, ha, ?_⟩
  intro i j hij
  rw [hp i, hp j] at hij
  have hnorm : ‖z i‖ = ‖z j‖ := by
    have he := congrArg norm hij
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_norm, hb, mul_one] using he
  rw [hnorm] at hij
  by_cases hj : z j = 0
  · have hi : z i = 0 := norm_eq_zero.mp (by simpa [hj] using hnorm)
    exact hz i j hi hj
  · have hne : (‖z j‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hj)
    have hpow : b i = b j := mul_left_cancel₀ hne hij
    exact Fin.ext (hζ.pow_inj i.isLt j.isLt hpow)

/-- In particular phases separate every configuration with nonzero coordinates. -/
theorem exists_coordinatePhase_collisionFree (n : ℕ) (hn : 0 < n)
    (z : Configuration n) (hz : ∀ i, z i ≠ 0) :
    ∃ a : Fin n → ℂ, (∀ i, ‖a i‖ = 1) ∧ CollisionFree (coordinatePhase a z) :=
  exists_coordinatePhase_collisionFree_of_zero_injective n hn z
    (fun i _ hi _ => (hz i hi).elim)

end
end GinibrePoincare
