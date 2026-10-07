module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalPath

@[expose] public section

/-! Lifespan bounds and the actual local regularity of the glued maximal path. -/
open Set Filter MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreDrivenHorizons_le_lifetime {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {T : ℝ≥0} (hT : T ∈ ginibreDrivenHorizons n α N z) :
    (T : ℝ≥0∞) ≤ ginibreDrivenMaximalLifetime n α N z :=
  le_iSup_of_le ⟨T, hT⟩ le_rfl

def ginibreDrivenMaximalDomain (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (z : Configuration n) : Set ℝ :=
  {t | 0 ≤ t ∧ ENNReal.ofReal t < ginibreDrivenMaximalLifetime n α N z}

theorem ginibreDrivenMaximalPath_continuousOn (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) :
    ContinuousOn (ginibreDrivenMaximalPath n α N z) (ginibreDrivenMaximalDomain n α N z) := by
  intro t ht
  obtain ⟨b, htb, hb⟩ := exists_between ht.2
  have hbtop : b ≠ ⊤ := (hb.trans_le le_top).ne
  let B : ℝ≥0 := b.toNNReal
  have hB : (B : ℝ≥0∞) < ginibreDrivenMaximalLifetime n α N z := by
    simpa only [B, ENNReal.coe_toNNReal hbtop] using hb
  have htB : t < (B : ℝ) := by
    apply (ENNReal.ofReal_lt_coe_iff ht.1).mp
    simpa only [B, ENNReal.coe_toNNReal hbtop] using htb
  have hs := ginibreDrivenMaximalPath_segment B hB
  apply (hs.1 t ⟨ht.1, htB.le⟩).mono_of_mem_nhdsWithin
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htB)] with u hu huB
  exact ⟨hu.1, huB.le⟩

theorem ginibreDrivenMaximalPath_initial (n : ℕ) (α : ℝ) (N : ℝ → Configuration n)
    (hN : Continuous N) (hN0 : N 0 = 0) (z : Configuration n) (hz : CollisionFree z) :
    ginibreDrivenMaximalPath n α N z 0 = z := by
  have hp := ginibreDrivenMaximalLifetime_pos n α N hN hN0 z hz
  exact (ginibreDrivenMaximalPath_segment 0 (by simpa using hp)).2.1

 theorem ginibreDrivenMaximalPath_equation {n : ℕ} {α : ℝ} {N : ℝ → Configuration n}
    {z : Configuration n} {t : ℝ} (ht : t ∈ ginibreDrivenMaximalDomain n α N z) :
    CollisionFree (ginibreDrivenMaximalPath n α N z t) ∧
      IntervalIntegrable (fun u => ginibreLangevinDrift n α (ginibreDrivenMaximalPath n α N z u)) volume 0 t ∧
      ginibreDrivenMaximalPath n α N z t = z+N t+
        ∫ u in (0 : ℝ)..t, ginibreLangevinDrift n α (ginibreDrivenMaximalPath n α N z u) := by
  have hs := ginibreDrivenMaximalPath_segment (Real.toNNReal t) ht.2
  exact hs.2.2 t ⟨ht.1, by rw [Real.coe_toNNReal t ht.1]⟩

end
end GinibrePoincare
