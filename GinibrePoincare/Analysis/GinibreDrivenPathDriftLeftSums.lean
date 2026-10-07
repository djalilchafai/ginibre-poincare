module

public import GinibrePoincare.Analysis.GinibreDrivenPathQuadraticCross

@[expose] public section

/-! Left sums against a smooth drift converge to the actual ordinary integral. -/
open MeasureTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem ginibreUniformDriftLeftSum_tendsto_integral (A A' X : ℝ → ℝ)
    (hA : ∀ s, HasDerivAt A (A' s) s) (hA' : Continuous A') (hX : Continuous X)
    (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => ∑ i ∈ Finset.range (n+1), X (ginibreUniformTime t n i)*
      (A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))) atTop
      (𝓝 (∫ s in (0 : ℝ)..t, X s*A' s)) := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 t) hA'.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, ht⟩)
  have hLip : LipschitzOnWith ⟨C,hC0⟩ A (Icc 0 t) :=
    (convex_Icc (0 : ℝ) t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (hA s).hasDerivWithinAt) (fun s hs => by exact_mod_cast hC s hs)
  have hc := ginibreUniformQuadraticCross_tendsto_zero A X t ht ⟨C,hC0⟩ hLip hX
  have hw := ginibreWeightedUniformIncrements_tendsto_integral A A' X hA hA' hX t ht
  simp only [smul_eq_mul] at hw
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => A t*X t-A 0*X 0) atTop
    (𝓝 (A t*X t-A 0*X 0))).sub hw).sub hc
  have hlim : A t*X t-A 0*X 0-(A t*X t-A 0*X 0-∫ s in (0 : ℝ)..t, A' s*X s)-0 =
      ∫ s in (0 : ℝ)..t, X s*A' s := by
    simp only [sub_zero, sub_sub_cancel]
    apply intervalIntegral.integral_congr
    intro s hs
    ring
  rw [hlim] at h
  convert h using 1
  funext n
  have hp := ginibreWeightedIncrements_by_parts
    (fun i => A (ginibreUniformTime t n i)) (fun i => X (ginibreUniformTime t n i)) (n+1)
  simp only [smul_eq_mul, ginibreUniformTime_end, ginibreUniformTime_zero] at hp
  have hs : (∑ i ∈ Finset.range (n+1), X (ginibreUniformTime t n i)*
      (A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i)))+
      (∑ i ∈ Finset.range (n+1), (A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))*
        (X (ginibreUniformTime t n (i+1))-X (ginibreUniformTime t n i))) =
      ∑ i ∈ Finset.range (n+1), (A (ginibreUniformTime t n (i+1))-A (ginibreUniformTime t n i))*
        X (ginibreUniformTime t n (i+1)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  linarith

end
end GinibrePoincare
