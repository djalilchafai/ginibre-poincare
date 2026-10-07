module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalLifetime

@[expose] public section

/-! The actual canonical maximal evaluation is continuous in time wherever alive. -/
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenMaximalValue_continuousAt_time {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n} (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z) :
    ContinuousAt (ginibreDrivenMaximalValue n α N z) t := by
  obtain ⟨b, htb, hb⟩ := exists_between ht
  have hbtop : b ≠ ⊤ := (hb.trans_le le_top).ne
  let B : ℝ≥0 := b.toNNReal
  have hB : (B : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
    simpa only [B, ENNReal.coe_toNNReal hbtop] using hb
  have htB : t < B := by
    apply ENNReal.coe_lt_coe.mp
    simpa only [B, ENNReal.coe_toNNReal hbtop] using htb
  have maps : MapsTo (fun u : ℝ≥0 => (u : ℝ)) (Iio B)
      (ginibreDrivenMaximalDomain n α N z) := by
    intro u hu
    refine ⟨u.coe_nonneg, ?_⟩
    rw [ENNReal.ofReal_coe_nnreal]
    exact (ENNReal.coe_lt_coe.mpr hu).trans hB
  have hc := (ginibreDrivenMaximalPath_continuousOn n α N z).comp
    NNReal.continuous_coe.continuousOn maps
  have hh := (hc t htB).continuousAt (isOpen_Iio.mem_nhds htB)
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe, Function.comp_def] using hh

end
end GinibrePoincare
