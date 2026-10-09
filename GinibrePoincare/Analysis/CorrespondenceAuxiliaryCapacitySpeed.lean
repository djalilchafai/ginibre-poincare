module

public import GinibrePoincare.Analysis.GinibreCollisionCapacity

@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- Ordinary weighted H¹ capacity at the paper's arbitrary speed α and
inverse temperature n², with actual distributional-gradient admissibility. -/
def ginibreCapacityCostsAtSpeed (n : ℕ) (α : ℝ) (C : Set (Configuration n)) : Set ℝ :=
  {r | ∃ (u : Configuration n → ℝ)
    (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hu : MemLp u 2 (ginibreMeasure n)) (hg : MemLp g 2 (ginibreMeasure n)),
    IsGinibreDistributionalGradient n (hu.toLp u) (hg.toLp g) ∧
    (∃ U : Set (Configuration n), IsOpen U ∧ C ⊆ U ∧ ∀ z ∈ U, 1 ≤ u z) ∧
    r = (∫ z, u z^2 ∂ginibreMeasure n) +
      (α / (n : ℝ)^2)*(∫ z, ‖g z‖^2 ∂ginibreMeasure n)}

def ginibreCapacityAtSpeed (n : ℕ) (α : ℝ) (C : Set (Configuration n)) : ℝ :=
  sInf (ginibreCapacityCostsAtSpeed n α C)

private theorem costsAtSpeed_nonneg (n : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (C : Set (Configuration n)) {r : ℝ}
    (hr : r ∈ ginibreCapacityCostsAtSpeed n α C) : 0 ≤ r := by
  obtain ⟨u, g, hu, hg, hw, hU, rfl⟩ := hr
  exact add_nonneg (integral_nonneg (fun z => sq_nonneg _))
    (mul_nonneg (div_nonneg hα (sq_nonneg _))
      (integral_nonneg (fun z => sq_nonneg _)))

/-- Zero collision capacity for every positive speed, including n=1. -/
theorem ginibreCollisionSet_capacity_zero_atSpeed (n : ℕ) (hn : 0 < n)
    (α : ℝ) (hα : 0 < α) : ginibreCapacityAtSpeed n α (collisionSet n) = 0 := by
  let C := collisionSet n
  let M := max 1 (α/(n : ℝ))
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hb : BddBelow (ginibreCapacityCosts n C) :=
    ⟨0, fun r hr => ginibreCapacityCosts_nonnegative n C hr⟩
  have hex : ∀ r ∈ ginibreCapacityCosts n C,
      ∃ q ∈ ginibreCapacityCostsAtSpeed n α C, q ≤ M*r := by
    intro r hr
    obtain ⟨u, g, hu, hg, hw, hU, rfl⟩ := hr
    let A := ∫ z, u z^2 ∂ginibreMeasure n
    let B := ∫ z, ‖g z‖^2 ∂ginibreMeasure n
    refine ⟨A+(α/(n : ℝ)^2)*B, ⟨u, g, hu, hg, hw, hU, rfl⟩,?_⟩
    have ha : 0 ≤ A := integral_nonneg fun z => sq_nonneg _
    have hb0 : 0 ≤ B := integral_nonneg fun z => sq_nonneg _
    have hm1 : 1 ≤ M := le_max_left _ _
    have hmα : α/(n : ℝ) ≤ M := le_max_right _ _
    have hc : α/(n : ℝ)^2 ≤ M*(1/(n : ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hmα (le_of_lt (inv_pos.mpr hnR))
      simpa only [div_eq_mul_inv, pow_two, inv_mul_cancel₀ hnR.ne', one_mul,
        mul_inv_rev, mul_assoc] using h
    change A+α/(n : ℝ)^2*B ≤ M*(A+(1/(n : ℝ))*B)
    calc
      _ ≤ M*A+(M*(1/(n : ℝ)))*B :=
        add_le_add (by nlinarith) (mul_le_mul_of_nonneg_right hc hb0)
      _ = _ := by ring
  obtain ⟨r, hr⟩ := ginibreCapacityCosts_nonempty hn C
  obtain ⟨q, hq, hbound⟩ := hex r hr
  have hbelow : BddBelow (ginibreCapacityCostsAtSpeed n α C) :=
    ⟨0, fun q hq => costsAtSpeed_nonneg n α hα.le C hq⟩
  have hnonempty : (ginibreCapacityCostsAtSpeed n α C).Nonempty := ⟨q, hq⟩
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hsinf : sInf (ginibreCapacityCosts n C) = 0 := ginibreCollisionSet_capacity_zero hn
    have hlt : sInf (ginibreCapacityCosts n C) < ε/M := by rw [hsinf]; exact div_pos hε hM
    obtain ⟨r, hr, hrlt⟩ := (csInf_lt_iff hb (ginibreCapacityCosts_nonempty hn C)).mp hlt
    obtain ⟨q, hq, hqr⟩ := hex r hr
    have hcost : ginibreCapacityAtSpeed n α C ≤ q := csInf_le hbelow hq
    have hbound : M*r < ε := (lt_div_iff₀ hM).mp hrlt |> fun h => by simpa [mul_comm] using h
    dsimp [C] at hcost
    linarith
  · exact le_csInf hnonempty (fun q hq => costsAtSpeed_nonneg n α hα.le C hq)

#print axioms ginibreCollisionSet_capacity_zero_atSpeed
end
end GinibrePoincare
