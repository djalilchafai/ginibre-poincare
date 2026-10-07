module

public import GinibrePoincare.Analysis.GinibreArbitraryWeakPairClosure
public import GinibrePoincare.Analysis.GinibreGraphNormEquivalence

@[expose] public section

/-! # Real smooth core closure equivalence

The global and collision-free compact smooth real gradient graphs have exactly
the same closure: the independently defined distributional gradient graph.
This supplies the real part of the core assertion in arXiv v2 Lemma A.2.
-/

open MeasureTheory
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- All compact smooth real value-gradient pairs, with no support restriction. -/
def ginibreGlobalRealSmoothPairs (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | ∃ f : Configuration n → ℝ, ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧
    (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f}

theorem ginibreRealInteriorCore_closure_eq_distributional (n : ℕ) (hn : 0 < n) :
    closure (ginibreInteriorSmoothPair n) =
      {p | IsGinibreDistributionalGradient n p.1 p.2} := by
  apply Set.Subset.antisymm
  · apply closure_minimal _ (isClosed_ginibre_distributional_gradient_pairs n hn)
    rintro p ⟨f, hs, _, _, hu, hg⟩
    exact ginibre_smooth_distributional_gradient n hn p.1 p.2 f hs hu hg
  · intro p hp
    exact ginibreWeakPair_mem_closure_interiorSmooth hn p.1 p.2 hp

/-- Global and collision-free compact smooth cores have the same real graph closure. -/
theorem ginibreRealSmoothCore_closure_equivalence (n : ℕ) (hn : 0 < n) :
    closure (ginibreGlobalRealSmoothPairs n) = closure (ginibreInteriorSmoothPair n) := by
  apply Set.Subset.antisymm
  · rw [ginibreRealInteriorCore_closure_eq_distributional n hn]
    apply closure_minimal _ (isClosed_ginibre_distributional_gradient_pairs n hn)
    rintro p ⟨f, hs, _, hu, hg⟩
    exact ginibre_smooth_distributional_gradient n hn p.1 p.2 f hs hu hg
  · apply closure_mono
    rintro p ⟨f, hs, hc, _, hu, hg⟩
    exact ⟨f, hs, hc, hu, hg⟩

end
end GinibrePoincare

#print axioms GinibrePoincare.ginibreRealInteriorCore_closure_eq_distributional
#print axioms GinibrePoincare.ginibreRealSmoothCore_closure_equivalence
