module

public import GinibrePoincare.Analysis.GinibreDrivenPathOUUniqueness
public import GinibrePoincare.Analysis.GinibreStochasticOUPath

@[expose] public section

/-! # Global pathwise uniqueness for the actual one-particle Ginibre equation -/
namespace GinibrePoincare
noncomputable section

 theorem ginibreDrivenPath_one_unique (α : ℝ) (N X : ℝ → Configuration 1)
    (hN : Continuous N) (hX : Continuous X) (hpath : IsGinibreDrivenPath 1 α N X)
    (t : ℝ) (ht : 0 ≤ t) :
    X t = drivenOUPath (2 * α) (X 0) N t := by
  apply drivenOUPath_unique_nonneg (2 * α) (X 0) N X hN hX _ t ht
  intro s hs
  simpa only [ginibreLangevinDrift_one] using hpath.2 s hs

/-- Two continuous actual solutions with the same cumulative noise and initial
point agree for every nonnegative time. -/
theorem ginibreDrivenPath_one_pathwise_unique (α : ℝ) (N X Y : ℝ → Configuration 1)
    (hN : Continuous N) (hX : Continuous X) (hY : Continuous Y)
    (hpathX : IsGinibreDrivenPath 1 α N X) (hpathY : IsGinibreDrivenPath 1 α N Y)
    (h0 : X 0 = Y 0) (t : ℝ) (ht : 0 ≤ t) : X t = Y t := by
  rw [ginibreDrivenPath_one_unique α N X hN hX hpathX t ht,
    ginibreDrivenPath_one_unique α N Y hN hY hpathY t ht, h0]

end
end GinibrePoincare
