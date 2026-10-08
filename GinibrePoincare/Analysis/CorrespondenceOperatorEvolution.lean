module
public import GinibrePoincare.Analysis.CorrespondenceOperatorComplex
public import GinibrePoincare.Analysis.GinibreFullSemigroupInfinitesimal
@[expose] public section
open scoped NNReal LinearPMap
namespace GinibrePoincare
noncomputable section
/-- Full-space contraction semigroup constructed from the actual weak resolvent. -/
def correspondenceOperatorEvolution (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    GinibreFullComplexL2 n →L[ℂ] GinibreFullComplexL2 n :=
  resolventCfcEvolution (correspondenceOperatorComplexResolvent n hn) t

@[simp] theorem correspondenceOperatorEvolution_zero (n : ℕ) (hn : 0 < n) :
    correspondenceOperatorEvolution n hn 0 = 1 :=
  resolventCfcEvolution_zero _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)

theorem correspondenceOperatorEvolution_add (n : ℕ) (hn : 0 < n) (s t : ℝ≥0) :
    correspondenceOperatorEvolution n hn (s + t) = correspondenceOperatorEvolution n hn s * correspondenceOperatorEvolution n hn t :=
  resolventCfcEvolution_add _ s t

theorem correspondenceOperatorEvolution_norm_le (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    ‖correspondenceOperatorEvolution n hn t‖ ≤ 1 :=
  resolventCfcEvolution_norm_le _ (correspondenceOperatorComplexResolvent_spectrum n hn) t

theorem correspondenceOperatorEvolution_contracts (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (f : GinibreFullComplexL2 n) : ‖correspondenceOperatorEvolution n hn t f‖ ≤ ‖f‖ :=
  resolventCfcEvolution_contracts _ (correspondenceOperatorComplexResolvent_spectrum n hn) t f

/-- Strong continuity holds for every actual unrestricted Ginibre L² observable. -/
theorem continuous_correspondenceOperatorEvolution (n : ℕ) (hn : 0 < n) (f : GinibreFullComplexL2 n) :
    Continuous (fun t : ℝ≥0 => correspondenceOperatorEvolution n hn t f) :=
  continuous_resolventCfcEvolution _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_spectrum n hn) (correspondenceOperatorComplexResolvent_denseRange n hn) f

/-- Every full evolution operator is self-adjoint. -/
theorem correspondenceOperatorEvolution_selfAdjoint (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    IsSelfAdjoint (correspondenceOperatorEvolution n hn t) :=
  resolventCfcEvolution_selfAdjoint _ t

/-- Hilbert-space positivity of every full evolution operator. -/
theorem correspondenceOperatorEvolution_isPositive (n : ℕ) (hn : 0 < n) (t : ℝ≥0) :
    (correspondenceOperatorEvolution n hn t).IsPositive :=
  resolventCfcEvolution_isPositive _ (correspondenceOperatorComplexResolvent_spectrum n hn) t

/-- The full-space generator is exactly the semigroup's right infinitesimal generator. -/
theorem correspondenceOperatorGenerator_graph_iff_right_derivative (n : ℕ) (hn : 0 < n)
    (u v : GinibreFullComplexL2 n) :
    (u, v) ∈ (correspondenceOperatorGenerator n hn).graph ↔
      HasDerivWithinAt (fun t : ℝ => correspondenceOperatorEvolution n hn (Real.toNNReal t) u)
        v (Set.Ici 0) 0 :=
  resolventGenerator_graph_iff_right_derivative _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_injective n hn) (correspondenceOperatorComplexResolvent_spectrum n hn)
    (correspondenceOperatorComplexResolvent_denseRange n hn) u v

/-- Full generator graph preservation, with no restriction to polynomial observables. -/
theorem correspondenceOperatorEvolution_preserves_generator_graph (n : ℕ) (hn : 0 < n)
    (t : ℝ≥0) (u v : GinibreFullComplexL2 n) (hp : (u, v) ∈ (correspondenceOperatorGenerator n hn).graph) :
    (correspondenceOperatorEvolution n hn t u, correspondenceOperatorEvolution n hn t v) ∈ (correspondenceOperatorGenerator n hn).graph :=
  resolventCfcEvolution_preserves_generator_graph _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_injective n hn) t u v hp
#print axioms continuous_correspondenceOperatorEvolution
#print axioms correspondenceOperatorGenerator_graph_iff_right_derivative
#print axioms correspondenceOperatorEvolution_preserves_generator_graph
end
end GinibrePoincare
