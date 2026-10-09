module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralUniformSums

@[expose] public section

/-! Actual common-grid oscillations control differences of Brownian sums. -/
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def brownianUniformRefinementMesh {Ω : Type*} (F : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n m : ℕ) : Ω → ℝ :=
  brownianCoefficientSampleMesh (κ := Fin ((n+1)*(m+1))) F
    (fun k => itoUniformNNTime T (n+1) (k.val/(m+1)))
    (fun k => itoUniformNNTime T (m+1) (k.val/(n+1)))

theorem brownianUniformLeftSum_difference_secondMoment_le_mesh {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (F : ℝ≥0 → Ω → ℝ)
    (hF : ∀ t, @Measurable Ω ℝ (ginibreBrownianAugmentedFiltration B P hB t) _ (F t))
    (hFi : ∀ t, MemLp (F t) 2 P) (T : ℝ≥0) (n m : ℕ) :
    (∫ ω, (brownianUniformLeftSum (B j) F T (n+1) ω-brownianUniformLeftSum (B j) F T (m+1) ω)^2 ∂P) ≤
      (T : ℝ)*(∫ ω, (brownianUniformRefinementMesh F T n m ω)^2 ∂P) := by
  let G := fun k : Fin ((n+1)*(m+1)) => fun ω =>
    F (itoUniformNNTime T (n+1) (k.val/(m+1))) ω-F (itoUniformNNTime T (m+1) (k.val/(n+1))) ω
  have hG (k : Fin ((n+1)*(m+1))) : MemLp (G k) 2 P := (hFi _).sub (hFi _)
  have hmax : Integrable (fun ω => (brownianUniformRefinementMesh F T n m ω)^2) P := by
    have hm : Measurable (brownianUniformRefinementMesh F T n m) :=
      brownianCoefficientSampleMesh_measurable F _ _ (fun t => (hF t).mono
        ((ginibreBrownianAugmentedFiltration B P hB).le t) le_rfl)
    apply Integrable.mono' (integrable_finsetSum Finset.univ (fun k _ => (hG k).integrable_sq))
      (hm.pow_const 2).aestronglyMeasurable
    apply Eventually.of_forall
    intro ω
    have he : ∃ k : Fin ((n+1)*(m+1)), brownianUniformRefinementMesh F T n m ω = ‖G k ω‖ := by
      obtain ⟨k, hk, he⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun k => ‖G k ω‖)
      exact ⟨k, he⟩
    obtain ⟨k, hk⟩ := he
    rw [hk, norm_pow, Real.norm_of_nonneg (norm_nonneg _)]
    simpa only [Real.norm_eq_abs, sq_abs] using
      (Finset.single_le_sum (fun i _ => sq_nonneg (G i ω)) (Finset.mem_univ k))
  have hle (k : Fin ((n+1)*(m+1))) : (∫ ω, (G k ω)^2 ∂P) ≤
      ∫ ω, (brownianUniformRefinementMesh F T n m ω)^2 ∂P := by
    apply integral_mono (hG k).integrable_sq hmax
    intro ω
    have hh : ‖G k ω‖ ≤ brownianUniformRefinementMesh F T n m ω :=
      Finset.le_sup' (f := fun k => ‖G k ω‖) (Finset.mem_univ k)
    simpa only [Real.norm_eq_abs, sq_abs] using pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [brownianUniformLeftSum_difference_secondMoment B P hB hind j F hF hFi T (n+1) (m+1) (Nat.succ_pos _) (Nat.succ_pos _)]
  calc
    _ ≤ (T : ℝ)/((n+1)*(m+1) : ℕ)*∑ _k : Fin ((n+1)*(m+1)),
        ∫ ω, (brownianUniformRefinementMesh F T n m ω)^2 ∂P :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hle k) (by positivity)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hp : (((n+1)*(m+1) : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp

end
end GinibrePoincare
