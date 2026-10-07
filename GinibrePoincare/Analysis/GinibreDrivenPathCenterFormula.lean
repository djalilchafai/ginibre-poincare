module

public import GinibrePoincare.Analysis.GinibreDrivenPathOUUniqueness

@[expose] public section

/-! # The exact OU convolution of the center of an actual driven Ginibre path -/
namespace GinibrePoincare
noncomputable section

 theorem ginibreDrivenPath_center_formula (n : ℕ) (α : ℝ)
    (N X : ℝ → Configuration n) (hN : Continuous N) (hX : Continuous X)
    (hpath : IsGinibreDrivenPath n α N X) (t : ℝ) (ht : 0 ≤ t) :
    coordinateSum (X t) = drivenOUPath (2 * α / (n : ℝ)) (coordinateSum (X 0))
      (fun s => coordinateSum (N s)) t := by
  exact drivenOUPath_unique_nonneg (2 * α / (n : ℝ)) (coordinateSum (X 0))
    (fun s => coordinateSum (N s)) (fun s => coordinateSum (X s))
    (by simpa only [Function.comp_def, coordinateSumCLM_apply] using
      (coordinateSumCLM n).continuous.comp hN)
    (by simpa only [Function.comp_def, coordinateSumCLM_apply] using
      (coordinateSumCLM n).continuous.comp hX)
    (ginibreDrivenPath_center_equation n α N X hpath) t ht

end
end GinibrePoincare
