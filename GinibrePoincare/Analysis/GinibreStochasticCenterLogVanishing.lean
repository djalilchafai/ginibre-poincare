module

public import GinibrePoincare.Analysis.GinibreStochasticCenterSmallProbability

@[expose] public section

/-! The derived logarithmic estimates force zero center-hitting probability;
this elementary step uses genuine positive initial radius. -/
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibre_probability_zero_of_log_barriers {p C r d : ℝ}
    (hp : 0 ≤ p) (hC : 0 < C) (hr : 0 < r)
    (hb : ∀ ε : ℝ, 0 < ε → p ≤
      (Real.log (C+ε)-Real.log (r+ε)+d)/(Real.log (C+ε)-Real.log ε)) : p=0 := by
  by_contra hn
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hn)
  obtain ⟨k,hk⟩ := exists_nat_gt ((Real.log (C+1)-Real.log r+d-p*Real.log C)/p)
  let ε := Real.exp (-(k : ℝ))
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg k))
  have hden : 0 < Real.log (C+ε)-Real.log ε := sub_pos.mpr
    (Real.log_lt_log hε (by linarith))
  have hmul := (le_div_iff₀ hden).mp (hb ε hε)
  have hlo : Real.log C ≤ Real.log (C+ε) := Real.log_le_log hC (by linarith)
  have hhi : Real.log (C+ε) ≤ Real.log (C+1) := Real.log_le_log (by positivity) (by linarith)
  have hri : Real.log r ≤ Real.log (r+ε) := Real.log_le_log hr (by linarith)
  have he : Real.log ε=-(k : ℝ) := Real.log_exp _
  rw [he] at hmul
  have hlow := mul_le_mul_of_nonneg_left hlo hp
  have hk' := (div_lt_iff₀ hpp).mp hk
  nlinarith
end
end GinibrePoincare
