module

public import GinibrePoincare.Analysis.MatrixGaussianLSI

@[expose] public section

open MeasureTheory Filter
open scoped Topology ContDiff NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MatrixRealSpace (n : ℕ) := Fin n → Fin n → ℂ

def matrixSpatialBump (n : ℕ) : ContDiffBump (0 : MatrixRealSpace n) :=
  ⟨1, 2, by norm_num, by norm_num⟩

def matrixSpatialCutoff (n k : ℕ) (A : MatrixRealSpace n) : ℝ :=
  matrixSpatialBump n (((k : ℝ) + 1)⁻¹ • A)

theorem matrixSpatialCutoff_smooth (n k : ℕ) : ContDiff ℝ ∞ (matrixSpatialCutoff n k) :=
  (matrixSpatialBump n).contDiff.comp (by fun_prop)

theorem matrixSpatialCutoff_compact (n k : ℕ) : HasCompactSupport (matrixSpatialCutoff n k) := by
  exact (matrixSpatialBump n).hasCompactSupport.comp_homeomorph
    (Homeomorph.smulOfNeZero (((k : ℝ) + 1)⁻¹) (inv_ne_zero (by positivity)))

theorem matrixSpatialCutoff_mem_unit (n k : ℕ) (A : MatrixRealSpace n) :
    0 ≤ matrixSpatialCutoff n k A ∧ matrixSpatialCutoff n k A ≤ 1 :=
  ⟨(matrixSpatialBump n).nonneg, (matrixSpatialBump n).le_one⟩

theorem matrixSpatialCutoff_tendsto (n : ℕ) (A : MatrixRealSpace n) :
    Tendsto (fun k => matrixSpatialCutoff n k A) atTop (nhds 1) := by
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  have hx := hi.smul_const A
  have hz : matrixSpatialBump n (0 : MatrixRealSpace n) = 1 :=
    (matrixSpatialBump n).one_of_mem_closedBall (by simp [matrixSpatialBump])
  simpa [matrixSpatialCutoff, hz, Function.comp_def] using
    ((matrixSpatialBump n).continuous.continuousAt.tendsto.comp hx)

theorem matrixSpatialCutoff_fderiv (n k : ℕ) (A H : MatrixRealSpace n) :
    fderiv ℝ (matrixSpatialCutoff n k) A H =
      ((k : ℝ) + 1)⁻¹ * fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
        (((k : ℝ) + 1)⁻¹ • A) H := by
  have hd := (((matrixSpatialBump n).contDiff (n := 1)).differentiable (by norm_num)
    (((k : ℝ) + 1)⁻¹ • A)).hasFDerivAt.comp A
      ((hasFDerivAt_id A).const_smul (((k : ℝ) + 1)⁻¹))
  unfold matrixSpatialCutoff
  simpa [matrixSpatialCutoff, Function.comp_def, ContinuousLinearMap.comp_apply,
    map_smul, smul_eq_mul] using congrArg (fun L : MatrixRealSpace n →L[ℝ] ℝ => L H) hd.fderiv

#print axioms matrixSpatialCutoff_fderiv

theorem matrixSpatialCutoff_derivative_bound (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ k (A H : MatrixRealSpace n),
      |fderiv ℝ (matrixSpatialCutoff n k) A H| ≤ M / ((k : ℝ) + 1) * ‖H‖ := by
  obtain ⟨M, hM⟩ := ((matrixSpatialBump n).contDiff (n := 1)).continuous_fderiv one_ne_zero
    |>.bounded_above_of_compact_support ((matrixSpatialBump n).hasCompactSupport.fderiv ℝ)
  refine ⟨M, (norm_nonneg _).trans (hM 0), ?_⟩
  intro k A H
  rw [matrixSpatialCutoff_fderiv, abs_mul, abs_of_nonneg (by positivity)]
  have hnorm := (fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
    (((k : ℝ) + 1)⁻¹ • A)).le_opNorm H
  have hh : |fderiv ℝ (matrixSpatialBump n : MatrixRealSpace n → ℝ)
      (((k : ℝ) + 1)⁻¹ • A) H| ≤ M * ‖H‖ :=
    hnorm.trans (mul_le_mul_of_nonneg_right (hM _) (norm_nonneg H))
  calc
    _ ≤ ((k : ℝ) + 1)⁻¹ * (M * ‖H‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem matrixSpatialCutoff_derivative_tendsto (n : ℕ) (A H : MatrixRealSpace n) :
    Tendsto (fun k => fderiv ℝ (matrixSpatialCutoff n k) A H) atTop (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := matrixSpatialCutoff_derivative_bound n
  have hi : Tendsto (fun k : ℕ => ((k : ℝ) + 1)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) (fun k => by simpa using hM k A H)
  simpa [div_eq_mul_inv] using (hi.const_mul M).mul_const ‖H‖

#print axioms matrixSpatialCutoff_derivative_tendsto
end
end GinibrePoincare
