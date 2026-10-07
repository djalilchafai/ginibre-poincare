module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity

@[expose] public section

/-! # Actual bounded multipliers on complex L² -/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem boundedMultiplier_memLp (b : X → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) (u : Lp ℂ 2 μ) : MemLp (fun x => b x * u x) 2 μ :=
  (Lp.memLp u).of_le_mul (hb.mul (Lp.aestronglyMeasurable u))
    (Filter.Eventually.of_forall (fun x => by rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)))

def boundedMultiplierLinearMap (b : X → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun u := (boundedMultiplier_memLp b hb C hC u).toLp _
  map_add' u v := by
    apply Lp.ext
    filter_upwards [(boundedMultiplier_memLp b hb C hC (u + v)).coeFn_toLp,
      Lp.coeFn_add u v,
      Lp.coeFn_add ((boundedMultiplier_memLp b hb C hC u).toLp _)
        ((boundedMultiplier_memLp b hb C hC v).toLp _),
      (boundedMultiplier_memLp b hb C hC u).coeFn_toLp,
      (boundedMultiplier_memLp b hb C hC v).coeFn_toLp] with x hl huv hr hu hv
    rw [hl, hr]
    change b x * (u + v) x = _
    change (u + v) x = u x + v x at huv
    change _ = (boundedMultiplier_memLp b hb C hC u).toLp _ x +
      (boundedMultiplier_memLp b hb C hC v).toLp _ x
    rw [huv, hu, hv]
    ring
  map_smul' c u := by
    simp only [RingHom.id_apply]
    apply Lp.ext
    filter_upwards [(boundedMultiplier_memLp b hb C hC (c • u)).coeFn_toLp,
      Lp.coeFn_smul c u,
      Lp.coeFn_smul c ((boundedMultiplier_memLp b hb C hC u).toLp _),
      (boundedMultiplier_memLp b hb C hC u).coeFn_toLp] with x hl hcu hr hu
    rw [hl, hr]
    change (c • u) x = c * u x at hcu
    change b x * (c • u) x = c * (boundedMultiplier_memLp b hb C hC u).toLp _ x
    rw [hcu, hu]
    ring

theorem boundedMultiplierLinearMap_bound (b : X → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) (u : Lp ℂ 2 μ) :
    ‖boundedMultiplierLinearMap b hb C hC u‖ ≤ C * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(boundedMultiplier_memLp b hb C hC u).coeFn_toLp] with x hx
  change ‖(boundedMultiplier_memLp b hb C hC u).toLp _ x‖ ≤ _
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

/-- Genuine multiplication by a bounded measurable scalar function, as an
actual continuous linear operator on the whole L² space. -/
def boundedComplexL2Multiplier (b : X → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (boundedMultiplierLinearMap b hb C hC).mkContinuous C (boundedMultiplierLinearMap_bound b hb C hC)

theorem boundedComplexL2Multiplier_coeFn (b : X → ℂ) (hb : AEStronglyMeasurable b μ)
    (C : ℝ) (hC : ∀ x, ‖b x‖ ≤ C) (u : Lp ℂ 2 μ) :
    (boundedComplexL2Multiplier b hb C hC u : X → ℂ) =ᵐ[μ] (fun x => b x * u x) :=
  (boundedMultiplier_memLp b hb C hC u).coeFn_toLp
end
end GinibrePoincare
