module

public import GinibrePoincare.Analysis.RadialWeakSobolevDomainApproximation

@[expose] public section

/-! # Equality of the independent radial weak domain and smooth-core completion -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Radial symmetric L² values remain radial symmetric under strong limits.
An almost-everywhere convergent subsequence supplies an actual radial representative. -/
theorem ginibreRadialL2Value_tendsto (n : ℕ)
    (v : ℕ → Lp ℝ 2 (ginibreMeasure n)) (u : Lp ℝ 2 (ginibreMeasure n))
    (hv : ∀ j, IsGinibreRadialL2Value n (v j)) (ht : Tendsto v atTop (𝓝 u)) :
    IsGinibreRadialL2Value n u := by
  classical
  simp only [IsGinibreRadialL2Value] at hv ⊢
  choose f hs hr hf using hv
  choose F hF using hr
  obtain ⟨ns, hns, hnae⟩ := (tendstoInMeasure_of_tendsto_Lp ht).exists_seq_tendsto_ae
  let l (z : Configuration n) := limUnder atTop (fun j => f (ns j) z)
  refine ⟨l, ?_, ?_, ?_⟩
  · intro σ z
    dsimp only [l]
    congr 1
    funext j
    exact hs (ns j) σ z
  · refine ⟨fun r => limUnder atTop (fun j => F (ns j) r), ?_⟩
    intro z
    dsimp only [l]
    congr 1
    funext j
    exact hF (ns j) z
  · filter_upwards [hnae, (ae_all_iff).mpr hf] with z hz hfz
    have he : (fun j => f (ns j) z) = (fun j => v (ns j) z) :=
      funext (fun j => (hfz (ns j)).symm)
    dsimp only [l]
    rw [he]
    exact hz.limUnder_eq.symm

/-- The independently radial symmetric value class is closed in actual Ginibre L². -/
theorem isClosed_ginibreRadialL2Values (n : ℕ) :
    IsClosed {u : Lp ℝ 2 (ginibreMeasure n) | IsGinibreRadialL2Value n u} := by
  apply IsSeqClosed.isClosed
  intro v u hv ht
  exact ginibreRadialL2Value_tendsto n v u hv ht

/-- The independent radial weak Sobolev graph is closed. -/
theorem isClosed_ginibreRadialWeakSobolevPairs (n : ℕ) (hn : 0 < n) :
    IsClosed (ginibreRadialWeakSobolevPairs n) := by
  exact (isClosed_ginibre_distributional_gradient_pairs n hn).inter
    ((isClosed_ginibreRadialL2Values n).preimage continuous_fst)

/-- Full equality of the independently defined radial weak-H¹ graph and the
original radial smooth-core completion, including unbounded noncompact values. -/
theorem ginibreRadialWeakSobolevPairs_eq_sobolevClosure (n : ℕ) (hn : 0 < n) :
    ginibreRadialWeakSobolevPairs n = radialSobolevClosure n := by
  apply Set.Subset.antisymm
  · exact ginibreRadialWeakSobolevPairs_subset_sobolevClosure n hn
  · exact closure_minimal
      ((radialSobolevCorePairs_subset_compact_weak n hn).trans
        (ginibreCompactRadialWeakSobolevPairs_subset n))
      (isClosed_ginibreRadialWeakSobolevPairs n hn)
end
end GinibrePoincare
