module
public import GinibrePoincare.Analysis.CorrespondenceOperatorEvolution
public import GinibrePoincare.Analysis.GinibreFullSemigroupConservation
@[expose] public section
open MeasureTheory Filter
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The unrestricted resolvent fixes every genuine equilibrium constant. -/
theorem correspondenceOperatorValueResolvent_constant (n : ℕ) (hn : 0<n) (c : ℝ) :
    correspondenceOperatorValueResolvent n hn (ginibreRealConstantL2 n hn c)=
      ginibreRealConstantL2 n hn c := by
  have he := correspondenceOperatorGenerator_resolvent_unique n hn
    (ginibreRealConstantL2 n hn c) (ginibreRealConstantL2 n hn c) 0
    (ginibreRealConstantL2_weak n hn c) (by intro v h hv; simp)
  exact he.1.symm

theorem correspondenceOperatorComplexResolvent_constant (n : ℕ) (hn : 0<n) (c : ℂ) :
    correspondenceOperatorComplexResolvent n hn (ginibreFullConstant n hn c).val =
      (ginibreFullConstant n hn c).val := by
  have hr : ginibreFullComplexRe n (ginibreFullConstant n hn c).val =
      ginibreRealConstantL2 n hn c.re := ginibreFullConstant_re n hn c
  have hi : ginibreFullComplexIm n (ginibreFullConstant n hn c).val =
      ginibreRealConstantL2 n hn c.im := ginibreFullConstant_im n hn c
  have hd := ginibreFullComplex_decomposition n
    (correspondenceOperatorComplexResolvent n hn (ginibreFullConstant n hn c).val)
  rw [correspondenceOperatorComplexResolvent_re, correspondenceOperatorComplexResolvent_im,
    hr, hi, correspondenceOperatorValueResolvent_constant, correspondenceOperatorValueResolvent_constant] at hd
  have hc := ginibreFullComplex_decomposition n (ginibreFullConstant n hn c).val
  rw [hr, hi] at hc
  exact hd.symm.trans hc

/-- Every constant belongs to the unrestricted generator kernel. -/
theorem correspondenceOperatorGenerator_constant (n : ℕ) (hn : 0<n) (c : ℂ) :
    ((ginibreFullConstant n hn c).val, 0) ∈ (correspondenceOperatorGenerator n hn).graph := by
  rw [correspondenceOperatorGenerator_graph_iff, sub_zero]
  exact correspondenceOperatorComplexResolvent_constant n hn c

/-- The unrestricted diffusion is conservative, preserving the literal
constant one (indeed every complex constant) at every nonnegative time. -/
theorem correspondenceOperatorEvolution_constant (n : ℕ) (hn : 0<n) (t : ℝ≥0) (c : ℂ) :
    correspondenceOperatorEvolution n hn t (ginibreFullConstant n hn c).val =
      (ginibreFullConstant n hn c).val :=
  resolventCfcEvolution_fixes_kernel _ (correspondenceOperatorComplexResolvent_isSelfAdjoint n hn)
    (correspondenceOperatorComplexResolvent_injective n hn) t _
    (correspondenceOperatorGenerator_constant n hn c)

#print axioms correspondenceOperatorEvolution_constant
#print axioms correspondenceOperatorGenerator_constant
end
end GinibrePoincare
