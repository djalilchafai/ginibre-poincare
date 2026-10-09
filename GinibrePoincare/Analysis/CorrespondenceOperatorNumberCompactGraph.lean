module
public import GinibrePoincare.Analysis.CorrespondenceOperatorNumberForm
public import GinibrePoincare.Analysis.AlternativeBochnerKodairaCompact
@[expose] public section
open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
/-- The actual differential number operator on every compact C∞ test belongs
to the maximal self-adjoint operator's graph. -/
theorem correspondenceOperatorNumber_compact_graph {n : ℕ} (hn : 0<n)
    (f : BKCompactTest n) :
    (f.l2, bkCompactNumberL2 f)∈(correspondenceOperatorNumber n hn).graph := by
  rw [correspondenceOperatorNumber_graph_iff_ordinary_form]
  refine ⟨fun j=>(f.dbar j).l2,?_,?_⟩
  · intro j
    exact gaussian_smooth_weak_dbar hn j f.l2 (f.dbar j).l2 f
      (f.smooth.of_le (by simp)) f.l2_coe (f.dbar j).l2_coe
  · intro w E hw
    unfold bkCompactNumberL2
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro j hj
    have h := hw j (f.dbar j) ((f.dbar j).smooth.of_le (by simp)) (f.dbar j).compact
    have he : gaussianDbarAdjointTestL2 j (f.dbar j)
        ((f.dbar j).smooth.of_le (by simp)) (f.dbar j).compact=((f.dbar j).adjoint j).l2 := by
      apply Lp.ext
      filter_upwards [(gaussianDbarAdjointTest_memLp j (f.dbar j)
        ((f.dbar j).smooth.of_le (by simp)) (f.dbar j).compact).coeFn_toLp,
        ((f.dbar j).adjoint j).l2_coe] with z hz hf
      exact hz.trans hf.symm
    rw [he] at h
    exact h.symm
#print axioms correspondenceOperatorNumber_compact_graph
end
end GinibrePoincare
