module

public import GinibrePoincare.Analysis.GinibreStochasticAugmentedWeightedDiagonal
public import GinibrePoincare.Analysis.GinibreStochasticAugmentedMixedVariation

@[expose] public section

/-! Actual full finite-dimensional predictable Hessian correction, including all off-diagonal terms. -/
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def ginibreBrownianAugmentedWeightedHessian {Ω ι : Type*} [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (A : ι → ι → ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ p : ι × ι, ∑ l : Fin (n+1), A p.1 p.2 (ginibreUniformBrownianTime t n l) ω*
    ((B p.1 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.1 (ginibreUniformBrownianTime t n l) ω)*
      (B p.2 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.2 (ginibreUniformBrownianTime t n l) ω))

theorem ginibreBrownianAugmentedWeightedHessian_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (t : ℝ≥0) (A : ι → ι → ℝ≥0 → Ω → ℝ)
    (hA : ∀ i j, StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) (A i j))
    (hc : ∀ i j, ∀ᵐ ω ∂P, Continuous (fun s => A i j s ω))
    (C : ℝ) (hbound : ∀ i j s ω, ‖A i j s ω‖ ≤ C) :
    TendstoInMeasure P (ginibreBrownianAugmentedWeightedHessian B t A) atTop
      (fun ω => ∑ i, ∫ s in (0 : ℝ)..t, A i i s.toNNReal ω) := by
  classical
  let W := fun (p : ι × ι) (n : ℕ) (ω : Ω) => ∑ l : Fin (n+1),
    A p.1 p.2 (ginibreUniformBrownianTime t n l) ω*
      ((B p.1 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.1 (ginibreUniformBrownianTime t n l) ω)*
        (B p.2 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.2 (ginibreUniformBrownianTime t n l) ω))
  let L := fun (p : ι × ι) (ω : Ω) => if p.1=p.2 then ∫ s in (0 : ℝ)..t, A p.1 p.2 s.toNNReal ω else 0
  have hBm (i : ι) (s : ℝ≥0) : Measurable (B i s) := aemeasurable_iff_measurable.mp ((hB i).aemeasurable s)
  have hWm (p : ι × ι) (n : ℕ) : AEStronglyMeasurable (W p n) P := by
    have hEach (l : Fin (n+1)) : AEStronglyMeasurable (fun ω =>
        A p.1 p.2 (ginibreUniformBrownianTime t n l) ω*
          ((B p.1 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.1 (ginibreUniformBrownianTime t n l) ω)*
            (B p.2 (ginibreUniformBrownianTime t n (l.val+1)) ω-B p.2 (ginibreUniformBrownianTime t n l) ω))) P :=
      (((hA _ _ _).mono ((ginibreBrownianAugmentedFiltration B P hB).le _)).aestronglyMeasurable).mul
        (((hBm _ _).sub (hBm _ _)).mul ((hBm _ _).sub (hBm _ _))).aestronglyMeasurable
    convert! Finset.aestronglyMeasurable_sum Finset.univ (fun l _ => hEach l) using 1
    ext ω
    simp [W]
  have hW (p : ι × ι) : TendstoInMeasure P (W p) atTop (L p) := by
    rcases p with ⟨i,j⟩
    by_cases hij : i=j
    · subst j
      convert! ginibreBrownianAugmentedWeightedDiagonal_tendstoInProbability B P hB hind i t (A i i)
          (hA i i) (hc i i) C (hbound i i) using 1
      all_goals simp [W,L,ginibreBrownianAugmentedWeightedDiagonal,pow_two]
      all_goals funext n ω; simp [ginibreBrownianAugmentedWeightedDiagonal,pow_two]
    · convert! ginibreBrownianAugmentedMixedError_tendstoInProbability B P hB hind i j hij t
        (fun n l => A i j (ginibreUniformBrownianTime t n l))
        (fun n l => (hA _ _ _).measurable) C (fun n l ω => hbound _ _ _ ω) using 1
      all_goals simp [W,L,hij,ginibreBrownianAugmentedMixedError]
  have h := itoTendstoInMeasure_finset_sum P Finset.univ W L hWm hW
  convert! h using 1
  ext ω
  simp [L,Fintype.sum_prod_type]

end
end GinibrePoincare
