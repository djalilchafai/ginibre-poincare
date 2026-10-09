module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticGraphUniqueness
public import GinibrePoincare.Analysis.GinibreFullSemigroupPaperSpeed

@[expose] public section

open Set
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Actual real full generator-domain orbits have their genuine derivative. -/
theorem ginibreFullRealEvolution_graph_derivative {n : ℕ} (hn : 0<n)
    (u v : ginibreFullSymmetricValues n)
    (hg : ginibreFullSymmetricResolvent n hn (u-v)=u)
    (t : ℝ) (ht : 0<t) :
    HasDerivAt (fun s : ℝ => ginibreFullRealEvolution n hn s.toNNReal u)
      (ginibreFullRealEvolution n hn t.toNNReal v) t := by
  have hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff,← map_sub, ginibreFullComplexResolvent_ofReal, hg]
  have hd := ginibreFullEvolution_hasDerivAt n hn _ _ hgraph ht
  exact (ginibreFullSymmetricRe n).hasFDerivAt.comp_hasDerivAt t hd

/-- The actual real semigroup preserves the full real weak generator graph. -/
theorem ginibreFullRealEvolution_preserves_graph {n : ℕ} (hn : 0<n)
    (u v : ginibreFullSymmetricValues n)
    (hg : ginibreFullSymmetricResolvent n hn (u-v)=u) (t : ℝ≥0) :
    ginibreFullSymmetricResolvent n hn
      (ginibreFullRealEvolution n hn t u-ginibreFullRealEvolution n hn t v)=
      ginibreFullRealEvolution n hn t u := by
  have hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph := by
    rw [ginibreFullGenerator_graph_iff,← map_sub, ginibreFullComplexResolvent_ofReal, hg]
  have hh := resolventCfcEvolution_preserves_generator_graph (ginibreFullComplexResolvent n hn)
    (ginibreFullComplexResolvent_isSelfAdjoint n hn) (ginibreFullComplexResolvent_injective n hn)
    t _ _ hgraph
  exact ((ginibreFullGenerator_graph_iff_real_imag hn _ _).mp hh).1

#print axioms ginibreFullRealEvolution_graph_derivative
#print axioms ginibreFullRealEvolution_preserves_graph
end
end GinibrePoincare
