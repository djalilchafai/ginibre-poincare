module

public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalBlowup

@[expose] public section

/-! Finite maximal lifetimes cross every Hamiltonian level before death. -/
open Set MeasureTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

 theorem ginibreDrivenMaximalPath_hamiltonian_continuousOn (n : ℕ) (α : ℝ)
    (N : ℝ → Configuration n) (z : Configuration n) :
    ContinuousOn (fun t => ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z t))
      (ginibreDrivenMaximalDomain n α N z) := by
  intro t ht
  exact (ginibreHamiltonian_contDiffAt n _
    (ginibreDrivenMaximalPath_equation ht).1).continuousAt.comp_continuousWithinAt
      (ginibreDrivenMaximalPath_continuousOn n α N z t ht)

 theorem ginibreDrivenMaximalLifetime_finite_hamiltonian_level {n : ℕ} (hn : 0 < n)
    (α : ℝ) (N : ℝ → Configuration n) (hN : Continuous N) (hN0 : N 0 = 0)
    (z : Configuration n) (hz : CollisionFree z)
    (hfin : ginibreDrivenMaximalLifetime n α N z ≠ ⊤)
    (R : ℝ) (hR : ginibreHamiltonian n z ≤ R) :
    ∃ t ∈ Ico 0 (ginibreDrivenMaximalLifetime n α N z).toReal,
      ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z t) = R := by
  obtain ⟨b, hb, hbR⟩ := ginibreDrivenMaximalLifetime_finite_hamiltonian_unbounded
    hn α N hN hN0 z hz hfin R
  have hc := (ginibreDrivenMaximalPath_hamiltonian_continuousOn n α N z).mono
    (show Icc 0 b ⊆ ginibreDrivenMaximalDomain n α N z from by
      rw [ginibreDrivenMaximalDomain_eq_Ico_of_finite hfin]
      intro u hu
      exact ⟨hu.1, hu.2.trans_lt hb.2⟩)
  have hzero := ginibreDrivenMaximalPath_initial n α N hN hN0 z hz
  obtain ⟨t, ht, hval⟩ := intermediate_value_Icc hb.1 hc
    (show R ∈ Icc (ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z 0))
      (ginibreHamiltonian n (ginibreDrivenMaximalPath n α N z b)) from by
      rw [hzero]
      exact ⟨hR, hbR.le⟩)
  exact ⟨t, ⟨ht.1, ht.2.trans_lt hb.2⟩, hval⟩

end
end GinibrePoincare
