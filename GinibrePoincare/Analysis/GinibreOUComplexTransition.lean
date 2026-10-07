module

public import GinibrePoincare.Analysis.GinibreOUTransitionSemigroup
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

@[expose] public section

/-! # Actual complex OU transition semigroup and coordinate transport -/
open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Transport an actual kernel through an actual measurable equivalence. -/
def ginibreTransportKernel {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (K : Kernel Y Y) : Kernel X X :=
  Kernel.deterministic e.symm e.symm.measurable ∘ₖ K ∘ₖ Kernel.deterministic e e.measurable

private theorem deterministic_equiv_inverse {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] (e : X ≃ᵐ Y) :
    Kernel.deterministic e e.measurable ∘ₖ Kernel.deterministic e.symm e.symm.measurable =
      Kernel.id := by
  rw [Kernel.deterministic_comp_deterministic]
  have he : (e : X → Y) ∘ e.symm = id := by funext y; simp
  simp only [he, Kernel.id]

theorem ginibreTransportKernel_comp {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (e : X ≃ᵐ Y) (K L : Kernel Y Y) :
    ginibreTransportKernel e L ∘ₖ ginibreTransportKernel e K =
      ginibreTransportKernel e (L ∘ₖ K) := by
  unfold ginibreTransportKernel
  simp only [Kernel.comp_assoc]
  rw [← Kernel.comp_assoc (Kernel.deterministic e e.measurable), deterministic_equiv_inverse,
    Kernel.id_comp]

def ginibreComplexRealProdEquiv : ℂ ≃ᵐ ℝ × ℝ :=
  Complex.equivRealProdCLM.toHomeomorph.toMeasurableEquiv

/-- Independent real and imaginary Gaussian coordinates define the actual
complex OU probability kernel. -/
def ginibreComplexOUTransition (rate t : ℝ≥0) : Kernel ℂ ℂ :=
  ginibreTransportKernel ginibreComplexRealProdEquiv
    (ginibreOUTransition rate t ∥ₖ ginibreOUTransition rate t)

instance ginibreComplexOUTransition_isMarkov (rate t : ℝ≥0) :
    IsMarkovKernel (ginibreComplexOUTransition rate t) := by
  unfold ginibreComplexOUTransition ginibreTransportKernel
  infer_instance

theorem ginibreComplexOUTransition_comp (rate s t : ℝ≥0) :
    ginibreComplexOUTransition rate t ∘ₖ ginibreComplexOUTransition rate s =
      ginibreComplexOUTransition rate (s + t) := by
  unfold ginibreComplexOUTransition
  rw [ginibreTransportKernel_comp, Kernel.parallelComp_comp_parallelComp,
    ginibreOUTransition_comp]

end
end GinibrePoincare
