module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberSecondBounds
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberForm
@[expose] public section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace GinibrePoincare
noncomputable section
open ComplexHermite
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
theorem correspondenceOperatorNumber_second_limits {n : ℕ} (hn : 0<n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u,v)∈(correspondenceOperatorNumber n hn).graph) :
    ∃Q : Fin n→Fin n→Lp ℂ 2 (complexGaussianMeasure n),∀j k,
      Tendsto (fun s=>correspondenceOperatorFiniteSecond n hn j k
        (gaussianHermiteFiniteCoefficients hn u s)) atTop (𝓝 (Q j k)) := by
  have hN := (correspondenceOperatorNumber_finite_core n hn u v huv).2
  have hC := hN.cauchySeq
  have hex (j k : Fin n) : ∃q : Lp ℂ 2 (complexGaussianMeasure n),
      Tendsto (fun s=>correspondenceOperatorFiniteSecond n hn j k
        (gaussianHermiteFiniteCoefficients hn u s)) atTop (𝓝 q) := by
    apply cauchySeq_tendsto_of_complete
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨S,hS⟩ := Metric.cauchySeq_iff.mp hC ε hε
    refine ⟨S,fun s hs t ht=>?_⟩
    exact lt_of_le_of_lt (correspondenceOperatorFiniteSecond_dist_le n hn j k _ _) (hS s hs t ht)
  choose Q hQ using hex
  exact ⟨Q,hQ⟩

/-- Equation (6.9) on the exact full maximal number domain, with every second
derivative an internally constructed ordinary distributional Gaussian derivative. -/
theorem correspondenceOperatorNumber_full_bochner_kodaira {n : ℕ} (hn : 0<n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (huv : (u,v)∈(correspondenceOperatorNumber n hn).graph) :
    ∃(D : Fin n→Lp ℂ 2 (complexGaussianMeasure n))
      (Q : Fin n→Fin n→Lp ℂ 2 (complexGaussianMeasure n)),
      (∀j,IsGaussianWeakDbar n u (D j) j) ∧
      (∀j k,IsGaussianWeakDbar n (D j) (Q j k) k) ∧
      ‖v‖^2=(∑j : Fin n,∑k : Fin n,‖Q j k‖^2)+(n:ℝ)*∑j : Fin n,‖D j‖^2 := by
  choose D hD using correspondenceOperatorNumber_weak_dbar_exists hn u v huv
  obtain ⟨Q,hQ⟩ := correspondenceOperatorNumber_second_limits hn u v huv
  have hDf := (gaussianWeakDbar_finiteHermite_approximation hn u D hD).2
  have hN := (correspondenceOperatorNumber_finite_core n hn u v huv).2
  refine ⟨D,Q,hD,?_,?_⟩
  · intro j k
    apply gaussianWeakDbar_of_tendsto (l := atTop) k
      (fun s=>(finiteDbarComponentL2 n hn (gaussianHermiteFiniteCoefficients hn u s) j,
        correspondenceOperatorFiniteSecond n hn j k (gaussianHermiteFiniteCoefficients hn u s)))
      (D j) (Q j k)
    · intro s
      rw [correspondenceOperatorFiniteSecond_eq]
      exact gaussian_finiteHermite_weak_dbar n hn
        (loweredCoefficients n (gaussianHermiteFiniteCoefficients hn u s) j) k
    · exact (hDf j).prodMk_nhds (hQ j k)
  · have hleft := hN.norm.pow 2
    have hsecond := tendsto_finsetSum Finset.univ (fun j _=>
      tendsto_finsetSum Finset.univ (fun k _=>(hQ j k).norm.pow 2))
    have hfirst := tendsto_finsetSum Finset.univ (fun j _=>(hDf j).norm.pow 2)
    have hright := hsecond.add (hfirst.const_mul (n:ℝ))
    apply tendsto_nhds_unique hleft
    apply hright.congr
    intro s
    simp only [correspondenceOperatorFiniteSecond_eq]
    exact (bkFinite_integrated_identity n hn (gaussianHermiteFiniteCoefficients hn u s)).symm
#print axioms correspondenceOperatorNumber_second_limits
#print axioms correspondenceOperatorNumber_full_bochner_kodaira
end
end GinibrePoincare
