module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevRoots
public import Mathlib.Analysis.Polynomial.CauchyBound
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Topology.MetricSpace.Sequences
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

/-! # Continuous symmetric spectral values across all matrix collisions -/
open scoped BigOperators Topology NNReal Matrix
open Matrix Polynomial Filter MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem continuous_matrix_charpoly_coeff (n k : ℕ) :
    Continuous (fun A : Matrix (Fin n) (Fin n) ℂ => A.charpoly.coeff k) := by
  classical
  by_cases hk : k ≤ n
  · have he : (fun A : Matrix (Fin n) (Fin n) ℂ => A.charpoly.coeff k) =
        fun A => (-1 : ℂ) ^ (n - k) * ∑ s ∈ Finset.univ.powersetCard (n - k),
          (A.submatrix (Subtype.val : s → Fin n) (Subtype.val : s → Fin n)).det := by
      funext A
      simpa only [Fintype.card_fin, Nat.sub_sub_self hk] using
        Matrix.charpoly_coeff_eq_sum_minors A (n - k) (by simp)
    rw [he]
    fun_prop
  · have he : (fun A : Matrix (Fin n) (Fin n) ℂ => A.charpoly.coeff k) = fun _ => 0 := by
      funext A
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
      omega
    rw [he]
    exact continuous_const

def matrixSpectralRootBound (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (∑ k ∈ Finset.range n, ‖A.charpoly.coeff k‖) + 1

theorem continuous_matrixSpectralRootBound (n : ℕ) : Continuous (matrixSpectralRootBound n) := by
  classical
  unfold matrixSpectralRootBound
  exact (continuous_finsetSum _ fun k _ => (continuous_matrix_charpoly_coeff n k).norm).add
    continuous_const

theorem matrix_root_norm_le_bound {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (hz : A.charpoly.IsRoot z) : ‖z‖ ≤ matrixSpectralRootBound n A := by
  classical
  have hr := hz.norm_lt_cauchyBound A.charpoly_monic.ne_zero
  have hs : Finset.sup (Finset.range n) (fun k => ‖A.charpoly.coeff k‖₊) ≤
      ∑ k ∈ Finset.range n, ‖A.charpoly.coeff k‖₊ := by
    apply Finset.sup_le
    intro k hk
    exact Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0) ≤ ‖A.charpoly.coeff j‖₊ from zero_le)) hk
  have hb : Polynomial.cauchyBound A.charpoly ≤
      (∑ k ∈ Finset.range n, ‖A.charpoly.coeff k‖₊) + 1 := by
    unfold Polynomial.cauchyBound
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, A.charpoly_monic.leadingCoeff]
    simpa using add_le_add_right hs 1
  have h := hr.le.trans hb
  unfold matrixSpectralRootBound
  have hreal := NNReal.coe_le_coe.mpr h
  simpa only [NNReal.coe_add, NNReal.coe_sum, NNReal.coe_one, coe_nnnorm] using hreal

theorem matrixAllEigenvalues_isRoot (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) :
    A.charpoly.IsRoot (matrixAllEigenvalues n A i) := by
  classical
  rw [Polynomial.IsRoot.def, matrixAllEigenvalues_charpoly, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp

theorem matrixAllEigenvalues_norm_le (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) :
    ‖matrixAllEigenvalues n A‖ ≤ matrixSpectralRootBound n A := by
  have hb : 0 ≤ matrixSpectralRootBound n A := by
    unfold matrixSpectralRootBound
    positivity
  apply (pi_norm_le_iff_of_nonneg hb).mpr
  intro i
  exact matrix_root_norm_le_bound A _ (matrixAllEigenvalues_isRoot n A i)

theorem continuous_roots_product_coeff (n k : ℕ) :
    Continuous (fun z : Fin n → ℂ => (∏ i, (Polynomial.X - Polynomial.C (z i))).coeff k) := by
  simpa only [Function.comp_def, Matrix.charpoly_diagonal] using (continuous_matrix_charpoly_coeff n k).comp
    (by fun_prop : Continuous (Matrix.diagonal : (Fin n → ℂ) → Matrix (Fin n) (Fin n) ℂ))

/-- Continuous particle-symmetric observables have continuous spectral lifts,
including every repeated eigenvalue configuration. -/
theorem continuous_matrixFullSymmetricSpectralLift (n : ℕ)
    (F : (Fin n → ℂ) → ℝ) (hF : Continuous F)
    (hsym : ∀ e : Fin n ≃ Fin n, ∀ z, F (z ∘ e) = F z) :
    Continuous (matrixFullSymmetricSpectralLift n F) := by
  classical
  letI : FirstCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  apply continuous_iff_isClosed.mpr
  intro C hC
  apply IsSeqClosed.isClosed
  intro u A hu hA
  obtain ⟨B, hB⟩ := ((continuous_matrixSpectralRootBound n).tendsto A |>.comp hA).bddAbove_range
  have hmem (k : ℕ) : matrixAllEigenvalues n (u k) ∈ Metric.closedBall 0 (max B 0) := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (matrixAllEigenvalues_norm_le n (u k)).trans
      ((hB ⟨k, rfl⟩).trans (le_max_left B 0))
  obtain ⟨z, hz, φ, hφ, hlim⟩ := (isCompact_closedBall (0 : Fin n → ℂ) (max B 0)).tendsto_subseq hmem
  have hchar : A.charpoly = ∏ i, (Polynomial.X - Polynomial.C (z i)) := by
    ext k
    have hleft := (continuous_matrix_charpoly_coeff n k).tendsto A |>.comp (hA.comp hφ.tendsto_atTop)
    have hright := (continuous_roots_product_coeff n k).tendsto z |>.comp hlim
    have heq : (fun j => (u (φ j)).charpoly.coeff k) =
        (fun j => (∏ i, (Polynomial.X - Polynomial.C (matrixAllEigenvalues n (u (φ j)) i))).coeff k) := by
      funext j
      rw [matrixAllEigenvalues_charpoly]
    exact tendsto_nhds_unique hleft (by simpa only [Function.comp_def, ← heq] using hright)
  have hval : F (matrixAllEigenvalues n A) = F z :=
    matrix_full_roots_symmetric_value A _ z (matrixAllEigenvalues_charpoly n A) hchar F hsym
  change F (matrixAllEigenvalues n A) ∈ C
  rw [hval]
  exact hC.mem_of_tendsto (hF.tendsto z |>.comp hlim) (Eventually.of_forall fun j => hu (φ j))

end
end GinibrePoincare
