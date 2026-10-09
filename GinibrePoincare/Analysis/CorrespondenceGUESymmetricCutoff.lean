module
public import GinibrePoincare.Analysis.CorrespondenceGUESpatialApproximation
public import GinibrePoincare.Analysis.CorrespondenceGUEPermutationGradient
@[expose] public section
open MeasureTheory Filter Set
open scoped BigOperators Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

def gueSymmetricSpatialCutoff (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹*∑σ : Equiv.Perm (Fin n), gueSpatialCutoff n k (guePermute n σ x)

theorem guePermute_mul (n : ℕ) (σ τ : Equiv.Perm (Fin n)) (x : EuclideanSpace ℝ (Fin n)) :
    guePermute n τ (guePermute n σ x)=guePermute n (σ*τ) x := rfl

theorem gueSymmetricSpatialCutoff_symmetric (n k : ℕ) (τ : Equiv.Perm (Fin n))
    (x : EuclideanSpace ℝ (Fin n)) :
    gueSymmetricSpatialCutoff n k (guePermute n τ x)=gueSymmetricSpatialCutoff n k x := by
  unfold gueSymmetricSpatialCutoff
  simp_rw [guePermute_mul]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft τ) (fun σ => gueSpatialCutoff n k (guePermute n σ x))

theorem gueSymmetricSpatialCutoff_smooth (n k : ℕ) : ContDiff ℝ ∞ (gueSymmetricSpatialCutoff n k) := by
  apply ContDiff.mul contDiff_const
  apply ContDiff.sum
  intro σ hσ
  exact (gueSpatialCutoff_smooth n k).comp (guePermuteIsometry n σ).contDiff

theorem gueSymmetricSpatialCutoff_compact (n k : ℕ) : HasCompactSupport (gueSymmetricSpatialCutoff n k) := by
  have hsum (s : Finset (Equiv.Perm (Fin n))) :
      HasCompactSupport (fun x => ∑σ∈s, gueSpatialCutoff n k (guePermute n σ x)) := by
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      change HasCompactSupport (0 : EuclideanSpace ℝ (Fin n)→ℝ)
      exact HasCompactSupport.zero
    | @insert σ s hσ ih =>
      simp_rw [Finset.sum_insert hσ]
      exact ((gueSpatialCutoff_compact n k).comp_homeomorph
        (guePermuteIsometry n σ).toHomeomorph).add ih
  exact (hsum Finset.univ).mul_left

theorem gueSymmetricSpatialCutoff_mem_unit (n k : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    0≤gueSymmetricSpatialCutoff n k x ∧ gueSymmetricSpatialCutoff n k x≤1 := by
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ)>0 := by exact_mod_cast Fintype.card_pos
  constructor
  · unfold gueSymmetricSpatialCutoff
    apply mul_nonneg (inv_nonneg.mpr hc.le)
    exact Finset.sum_nonneg (fun σ hσ => (gueSpatialCutoff_mem_unit n k _).1)
  · unfold gueSymmetricSpatialCutoff
    apply le_trans (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun σ hσ => (gueSpatialCutoff_mem_unit n k (guePermute n σ x)).2))
      (inv_nonneg.mpr hc.le))
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hc.ne']
    rfl

theorem gueSymmetricSpatialCutoff_tendsto (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => gueSymmetricSpatialCutoff n k x) atTop (nhds 1) := by
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  have ht := (tendsto_finsetSum Finset.univ (fun σ hσ => gueSpatialCutoff_tendsto n (guePermute n σ x))).const_mul
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  simpa only [gueSymmetricSpatialCutoff, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    inv_mul_cancel₀ hc] using ht


theorem gueSymmetricSpatialCutoff_fderiv (n k : ℕ) (x H : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (gueSymmetricSpatialCutoff n k) x H=
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹*∑σ : Equiv.Perm (Fin n),
        fderiv ℝ (gueSpatialCutoff n k) (guePermute n σ x) (guePermute n σ H) := by
  have hd σ : HasFDerivAt (fun y => gueSpatialCutoff n k (guePermute n σ y))
      ((fderiv ℝ (gueSpatialCutoff n k) (guePermute n σ x)).comp
        (guePermuteIsometry n σ).toContinuousLinearEquiv.toContinuousLinearMap) x :=
    ((gueSpatialCutoff_smooth n k).differentiable (by simp) _).hasFDerivAt.comp x
      (guePermuteIsometry n σ).toContinuousLinearEquiv.hasFDerivAt
  have hs := (HasFDerivAt.fun_sum (u := Finset.univ) (fun σ hσ => hd σ)).const_mul
    (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  unfold gueSymmetricSpatialCutoff
  simpa [guePermuteIsometry_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply] using congrArg (fun L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ => L H) hs.fderiv

theorem gueSymmetricSpatialCutoff_derivative_bound (n : ℕ) :
    ∃M : ℝ, 0≤M ∧ ∀k (x H : EuclideanSpace ℝ (Fin n)),
      |fderiv ℝ (gueSymmetricSpatialCutoff n k) x H|≤M/((k : ℝ)+1)*‖H‖ := by
  obtain ⟨M, hM0, hM⟩ := gueSpatialCutoff_derivative_bound n
  refine ⟨M, hM0, fun k x H => ?_⟩
  have hc : (Fintype.card (Equiv.Perm (Fin n)) : ℝ)>0 := by exact_mod_cast Fintype.card_pos
  rw [gueSymmetricSpatialCutoff_fderiv, abs_mul, abs_of_pos (inv_pos.mpr hc)]
  have hs : |∑σ : Equiv.Perm (Fin n), fderiv ℝ (gueSpatialCutoff n k) (guePermute n σ x) (guePermute n σ H)|≤
      ∑σ : Equiv.Perm (Fin n), M/((k : ℝ)+1)*‖H‖ := by
    apply le_trans (Finset.abs_sum_le_sum_abs _ _)
    apply Finset.sum_le_sum
    intro σ hσ
    have h := hM k (guePermute n σ x) (guePermute n σ H)
    have hnσ : ‖guePermute n σ H‖=‖H‖ := (guePermuteIsometry n σ).norm_map H
    rw [hnσ] at h
    exact h
  apply le_trans (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hc.le))
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

theorem gueSymmetricSpatialCutoff_derivative_tendsto (n : ℕ) (x H : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun k => fderiv ℝ (gueSymmetricSpatialCutoff n k) x H) atTop (nhds 0) := by
  simp_rw [gueSymmetricSpatialCutoff_fderiv]
  have ht := (tendsto_finsetSum Finset.univ (fun σ hσ =>
    gueSpatialCutoff_derivative_tendsto n (guePermute n σ x) (guePermute n σ H))).const_mul
      (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹
  simpa using ht

#print axioms gueSymmetricSpatialCutoff_derivative_bound

#print axioms gueSymmetricSpatialCutoff_symmetric
#print axioms gueSymmetricSpatialCutoff_tendsto
end
end GinibrePoincare
