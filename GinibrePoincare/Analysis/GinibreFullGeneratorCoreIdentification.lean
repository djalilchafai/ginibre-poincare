module

public import GinibrePoincare.Analysis.GinibreFullGeneratorSymmetry
public import GinibrePoincare.Analysis.GinibreFullSemigroup

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory
set_option backward.isDefEq.respectTransparency false

def ginibreFullCoreSymmetricValue {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullSymmetricValues n :=
  ⟨ginibreFullCoreValue hn f hf, fun σ => ((ginibreFullCorePair hn f hf).property.2 σ).1⟩

def ginibreFullCoreSymmetricPregenerator {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullSymmetricValues n :=
  ⟨ginibreFullCorePregenerator hn f hf, ginibreFullCorePregenerator_symmetric hn f hf⟩

theorem ginibreFullGenerator_real_core_resolvent {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ginibreFullSymmetricResolvent n hn
      (ginibreFullCoreSymmetricValue hn f hf - ginibreFullCoreSymmetricPregenerator hn f hf) =
      ginibreFullCoreSymmetricValue hn f hf := by
  apply Subtype.ext
  exact ginibreFullGenerator_resolvent_core hn f hf

@[simp] theorem ginibreFullComplexResolvent_ofReal (n : ℕ) (hn : 0 < n)
    (f : ginibreFullSymmetricValues n) :
    ginibreFullComplexResolvent n hn (ginibreFullSymmetricOfReal n f) =
      ginibreFullSymmetricOfReal n (ginibreFullSymmetricResolvent n hn f) := by
  change ginibreFullComplexResolventReal n hn _ = _
  simp [ginibreFullComplexResolventReal]

/-- Every concrete smooth collision-free symmetric core function lies in the
actual full symmetric generator graph, with its original pregenerator image. -/
theorem ginibreFullGenerator_core_graph {n : ℕ} (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    (ginibreFullSymmetricOfReal n (ginibreFullCoreSymmetricValue hn f hf),
      ginibreFullSymmetricOfReal n (ginibreFullCoreSymmetricPregenerator hn f hf)) ∈
      (ginibreFullGenerator n hn).graph := by
  rw [ginibreFullGenerator_graph_iff]
  rw [← map_sub, ginibreFullComplexResolvent_ofReal,
    ginibreFullGenerator_real_core_resolvent]

end GinibrePoincare
