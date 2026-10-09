module
public import GinibrePoincare.Analysis.CorrespondenceOperatorZeroGradient
public import GinibrePoincare.Analysis.CorrespondenceOperatorConservation
@[expose] public section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
/-- Exact unrestricted real resolvent fixed space, obtained from the ordinary
weak form energy and the proved zero-gradient constant theorem. -/
theorem correspondenceOperatorValueResolvent_fixed_iff_constant {n : ℕ} (hn : 0<n)
    (u : GinibreFullValueL2 n) :
    correspondenceOperatorValueResolvent n hn u=u ↔∃c : ℝ, u=ginibreRealConstantL2 n hn c := by
  constructor
  · intro hu
    let p := correspondenceOperatorFormResolvent n hn u
    let g := correspondenceOperatorFormGradient n hn p
    have hv : correspondenceOperatorFormValue n hn p=u := hu
    have he := correspondenceOperatorFormSpace_inner n hn p p
    have hR := correspondenceOperatorFormResolvent_riesz n hn u p
    rw [hv] at he hR
    rw [hR] at he
    have hginner : inner ℝ g g=0 := by
      change inner ℝ u u=inner ℝ u u+(1/(n : ℝ))*inner ℝ g g at he
      have hnR : 0<(1/(n : ℝ)) := by positivity
      nlinarith
    have hg : g=0 := inner_self_eq_zero.mp hginner
    have hw := correspondenceOperatorFormSpace_weak n hn p
    rw [hv] at hw
    change IsGinibreDistributionalGradient n u g at hw
    rw [hg] at hw
    exact correspondenceOperator_zero_gradient_constant hn u hw
  · rintro ⟨c, rfl⟩
    exact correspondenceOperatorValueResolvent_constant n hn c

/-- Exact fixed-space identification on the literal unrestricted complex L². -/
theorem correspondenceOperatorComplexResolvent_fixed_iff_constant {n : ℕ} (hn : 0<n)
    (u : GinibreFullComplexL2 n) :
    correspondenceOperatorComplexResolvent n hn u=u ↔
      ∃c : ℂ, u=(ginibreFullConstant n hn c).val := by
  constructor
  · intro hu
    have hr := congrArg (ginibreFullComplexRe n) hu
    have hi := congrArg (ginibreFullComplexIm n) hu
    rw [correspondenceOperatorComplexResolvent_re] at hr
    rw [correspondenceOperatorComplexResolvent_im] at hi
    obtain ⟨a, ha⟩ := (correspondenceOperatorValueResolvent_fixed_iff_constant hn _).mp hr
    obtain ⟨b, hb⟩ := (correspondenceOperatorValueResolvent_fixed_iff_constant hn _).mp hi
    refine ⟨⟨a, b⟩,?_⟩
    have hd := ginibreFullComplex_decomposition n u
    have hc := ginibreFullComplex_decomposition n (ginibreFullConstant n hn ⟨a, b⟩).val
    rw [ha, hb] at hd
    have hre : ginibreFullComplexRe n (ginibreFullConstant n hn ⟨a, b⟩).val=
        ginibreRealConstantL2 n hn a := ginibreFullConstant_re n hn ⟨a, b⟩
    have him : ginibreFullComplexIm n (ginibreFullConstant n hn ⟨a, b⟩).val=
        ginibreRealConstantL2 n hn b := ginibreFullConstant_im n hn ⟨a, b⟩
    rw [hre, him] at hc
    exact hd.symm.trans hc
  · rintro ⟨c, rfl⟩
    exact correspondenceOperatorComplexResolvent_constant n hn c
#print axioms correspondenceOperatorValueResolvent_fixed_iff_constant
#print axioms correspondenceOperatorComplexResolvent_fixed_iff_constant
end
end GinibrePoincare
