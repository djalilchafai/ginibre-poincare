module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalLifetime

@[expose] public section

/-! A finite canonical maximal lifetime forces actual Hamiltonian blow-up. -/
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreDrivenMaximalDomain_eq_Ico_of_finite {n : ℕ} {α : ℝ}
    {N : ℝ → Configuration n} {z : Configuration n}
    (hfin : ginibreDrivenMaximalLifetime n α N z ≠ ⊤) :
    ginibreDrivenMaximalDomain n α N z =
      Ico 0 (ginibreDrivenMaximalLifetime n α N z).toReal := by
  ext t
  unfold ginibreDrivenMaximalDomain
  simp only [Set.mem_setOf_eq, Set.mem_Ico]
  constructor
  · intro ht
    refine ⟨ht.1, ?_⟩
    rw [← ENNReal.coe_toNNReal hfin] at ht
    exact (ENNReal.ofReal_lt_coe_iff ht.1).mp ht.2
  · intro ht
    refine ⟨ht.1, ?_⟩
    rw [← ENNReal.coe_toNNReal hfin]
    exact (ENNReal.ofReal_lt_coe_iff ht.1).mpr ht.2

 theorem ginibreDrivenMaximalLifetime_finite_hamiltonian_unbounded {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z)
    (hfin : ginibreDrivenMaximalLifetime n α N z ≠ ⊤) :
    ∀ B : ℝ, ∃ t ∈ Ico 0 (ginibreDrivenMaximalLifetime n α N z).toReal,
      B < ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z t) := by
  let L := ginibreDrivenMaximalLifetime n α N z
  let T := L.toReal
  let X := ginibreDrivenMaximalPath n α N z
  have hL : 0 < L := ginibreDrivenMaximalLifetime_pos n α N hN hN0 z hz
  have hT : 0 < T := ENNReal.toReal_pos hL.ne' hfin
  have hdom : ginibreDrivenMaximalDomain n α N z = Ico 0 T :=
    ginibreDrivenMaximalDomain_eq_Ico_of_finite hfin
  have hX : ContinuousOn X (Ico 0 T) := by
    rw [← hdom]
    exact ginibreDrivenMaximalPath_continuousOn n α N z
  have hprops (t : ℝ) (ht : t ∈ Ico 0 T) :=
    ginibreDrivenMaximalPath_equation (n := n) (α := α) (N := N) (z := z) (hdom.symm ▸ ht)
  have hX0 : X 0 = z := ginibreDrivenMaximalPath_initial n α N hN hN0 z hz
  apply ginibreDrivenPath_finite_nonextendible_hamiltonian_unbounded hn α N X hN T hT hX
    (fun t ht => (hprops t ht).2.1)
    (fun t ht => by rw [hX0]; exact (hprops t ht).2.2)
    (fun t ht => (hprops t ht).1)
  rintro ⟨δ, hδ, U, heq, hU, hUEq⟩
  let S : ℝ≥0 := ⟨T+δ, by positivity⟩
  have hU0 : U 0 = z := (heq ⟨le_rfl, hT⟩).trans hX0
  have hs : S ∈ ginibreDrivenHorizons n α N z := by
    refine ⟨U, hU, hU0, ?_⟩
    intro t ht
    have hu := hUEq t ht
    exact ⟨hu.1, hu.2.1, by simpa only [hU0] using hu.2.2⟩
  have hle := ginibreDrivenHorizons_le_lifetime hs
  rw [← ENNReal.coe_toNNReal hfin] at hle
  have hreal : (S : ℝ) ≤ L.toReal := by exact_mod_cast (ENNReal.coe_le_coe.mp hle)
  change T+δ ≤ T at hreal
  linarith

end
end GinibrePoincare
