module

public import GinibrePoincare.Analysis.MatrixGaussianH1LSI

@[expose] public section

/-! # Compact gradient pairs and their Gaussian H¹ completion

`MatrixGaussianSobolevPair` stores a value and one real L² derivative for every
real matrix entry coordinate. Its H¹ completion is the closure of compact C¹
pairs in that product topology. The entropy bound extends to this closure using
the L² entropy limit theorem and continuity of the finite sum of derivative
norms. The core bound comes from the compact Lipschitz Gaussian inequality.

For a globally C¹ observable with finite value and gradient energy, expanding
matrix cutoffs give compact C¹ pairs. Their L² value and derivative errors tend
to zero, proving membership in the completion. Identification with ordinary weak
entry derivatives is handled by the separate Sobolev transport modules.
-/


open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev MatrixGaussianL2 (n : ℕ) := Lp ℝ 2 (matrixGaussianMeasure n)
abbrev MatrixGaussianSobolevPair (n : ℕ) :=
  MatrixGaussianL2 n × (MatrixRealIndex n → MatrixGaussianL2 n)

def matrixGaussianCompactC1Pairs (n : ℕ) : Set (MatrixGaussianSobolevPair n) :=
  {p | ∃ F : MatrixRealSpace n → ℝ, ContDiff ℝ 1 F ∧ HasCompactSupport F ∧
    (p.1 : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n] F ∧
    ∀ i, (p.2 i : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => fderiv ℝ F A (matrixRealCoordinates n (Pi.single i 1)))}

def matrixGaussianH1Completion (n : ℕ) : Set (MatrixGaussianSobolevPair n) :=
  closure (matrixGaussianCompactC1Pairs n)

def matrixGaussianSobolevEnergy (n : ℕ) (p : MatrixGaussianSobolevPair n) : ℝ :=
  ∑ i, ‖p.2 i‖ ^ 2

theorem matrixGaussian_entropy_energy_closed (n : ℕ) (c : ℝ) :
    IsClosed {p : MatrixGaussianSobolevPair n |
      Integrable (fun A => p.1 A ^ 2 * Real.log (p.1 A ^ 2)) (matrixGaussianMeasure n) ∧
        squareEntropy (matrixGaussianMeasure n) p.1 ≤ c * matrixGaussianSobolevEnergy n p} := by
  apply IsSeqClosed.isClosed
  intro p q hp hq
  apply squareEntropy_le_of_L2_tendsto (matrixGaussianMeasure n) (fun k => (p k).1) q.1
    (fun k => c * matrixGaussianSobolevEnergy n (p k)) (c * matrixGaussianSobolevEnergy n q)
    (continuous_fst.tendsto q |>.comp hq)
  · apply Tendsto.const_mul
    unfold matrixGaussianSobolevEnergy
    apply tendsto_finsetSum
    intro i hi
    exact ((continuous_apply i).tendsto q.2 |>.comp (continuous_snd.tendsto q |>.comp hq)).norm.pow 2
  · exact fun k => (hp k).1
  · exact fun k => (hp k).2

/-- The sharp inequality extends to the actual L² closure of all compact C¹
value/entry-gradient pairs. No core inequality or energy conclusion is assumed. -/
theorem matrixGaussianH1Completion_lsi (n : ℕ) (hn : 0 < n) :
    ∀ p ∈ matrixGaussianH1Completion n,
      Integrable (fun A => p.1 A ^ 2 * Real.log (p.1 A ^ 2)) (matrixGaussianMeasure n) ∧
        squareEntropy (matrixGaussianMeasure n) p.1 ≤
          (1 / (n : ℝ)) * matrixGaussianSobolevEnergy n p := by
  letI : OpensMeasurableSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (OpensMeasurableSpace (Fin n → Fin n → ℂ))
  letI : IsProbabilityMeasure (matrixGaussianMeasure n) := matrixGaussianMeasure_isProbability n
  letI : IsFiniteMeasureOnCompacts (matrixGaussianMeasure n) :=
    ⟨fun _ _ => measure_lt_top (matrixGaussianMeasure n) _⟩
  apply closure_minimal ?_ (matrixGaussian_entropy_energy_closed n (1 / (n : ℝ)))
  intro p hp
  obtain ⟨F, hF, hc, hv, hd⟩ := hp
  have hlog := (continuous_square_mul_log hF.continuous).integrable_of_hasCompactSupport
    (μ := (matrixGaussianMeasure n : Measure (MatrixRealSpace n))) (compactSupport_square_mul_log hc)
  refine ⟨hlog.congr ?_, ?_⟩
  · filter_upwards [hv] with A hA
    simp [hA]
  · rw [squareEntropy_congr_ae _ hv]
    obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hF one_ne_zero
    have hg := matrixGaussian_lsi_compactLipschitz n hn F hK hc
    have he : matrixGaussianSobolevEnergy n p =
        ∫ A, matrixRealGradientEnergy n F A ∂matrixGaussianMeasure n := by
      unfold matrixGaussianSobolevEnergy matrixRealGradientEnergy directionalEnergy
      simp_rw [← integral_square_eq_L2_norm_sq]
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro i hi
        apply integral_congr_ae
        filter_upwards [hd i] with A hA
        simp [hA]
      · intro i hi
        exact ((Lp.memLp (p.2 i)).ae_eq (hd i)).integrable_sq
    rw [he]
    exact hg

#print axioms matrixGaussianH1Completion_lsi

theorem matrixL2_toLp_dist_eq_sqrt (n : ℕ) (μ : Measure (MatrixRealSpace n))
    (F G : MatrixRealSpace n → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    dist (hF.toLp F) (hG.toLp G) = Real.sqrt (∫ A, (F A - G A) ^ 2 ∂μ) := by
  have he : (∫ A, (F A - G A) ^ 2 ∂μ) = ‖hF.toLp F - hG.toLp G‖ ^ 2 := by
    rw [← integral_square_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (hF.toLp F) (hG.toLp G), hF.coeFn_toLp, hG.coeFn_toLp]
      with A hA hFA hGA
    simp only [hA, Pi.sub_apply, hFA, hGA]
  rw [he, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), dist_eq_norm]

/-- Every actual C¹ finite-energy matrix observable belongs to the Gaussian H¹ completion. -/
theorem matrixGaussian_C1_pair_mem_H1Completion (n : ℕ)
    (F : MatrixRealSpace n → ℝ) (hF : ContDiff ℝ 1 F)
    (hv : MemLp F 2 (matrixGaussianMeasure n))
    (hD : ∀ i : MatrixRealIndex n, MemLp
      (fun A => fderiv ℝ F A (matrixRealCoordinates n (Pi.single i 1))) 2 (matrixGaussianMeasure n)) :
    (hv.toLp F, fun i => (hD i).toLp
      (fun A => fderiv ℝ F A (matrixRealCoordinates n (Pi.single i 1)))) ∈ matrixGaussianH1Completion n := by
  let μ : Measure (MatrixRealSpace n) := matrixGaussianMeasure n
  letI : IsProbabilityMeasure μ := matrixGaussianMeasure_isProbability n
  let g := fun k => matrixSpatialTruncation n k F
  let d := fun i : MatrixRealIndex n => matrixRealCoordinates n (Pi.single i 1)
  have hg (k : ℕ) := matrixSpatialTruncation_contDiff n k F hF
  have hc (k : ℕ) := matrixSpatialTruncation_compact n k F
  have htruncatedValue_memLp (k : ℕ) : MemLp (g k) 2 μ := (hg k).continuous.memLp_of_hasCompactSupport (hc k)
  have htruncatedDerivative_memLp (k : ℕ) (i : MatrixRealIndex n) : MemLp (fun A => fderiv ℝ (g k) A (d i)) 2 μ :=
    ((hg k).continuous_fderiv one_ne_zero).clm_apply continuous_const
      |>.memLp_of_hasCompactSupport ((hc k).fderiv_apply (𝕜 := ℝ) (d i))
  let P : ℕ → MatrixGaussianSobolevPair n := fun k =>
    ((htruncatedValue_memLp k).toLp (g k), fun i => (htruncatedDerivative_memLp k i).toLp (fun A => fderiv ℝ (g k) A (d i)))
  have hvalue_converges : Tendsto (fun k => (P k).1) atTop (nhds (hv.toLp F)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    change Tendsto (fun k => dist ((htruncatedValue_memLp k).toLp (g k)) (hv.toLp F)) atTop (nhds 0)
    simp_rw [matrixL2_toLp_dist_eq_sqrt]
    have hzero : MemLp (fun A : MatrixRealSpace n => fderiv ℝ F A 0) 2 μ := by simp
    simpa [g] using (matrixSpatialTruncation_L2_errors n μ F hF hv 0 hzero).1.sqrt
  have hgradient_converges : Tendsto (fun k => (P k).2) atTop
      (nhds (fun i => (hD i).toLp (fun A => fderiv ℝ F A (d i)))) := by
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_iff_dist_tendsto_zero.mpr
    change Tendsto (fun k => dist ((htruncatedDerivative_memLp k i).toLp (fun A => fderiv ℝ (g k) A (d i)))
      ((hD i).toLp (fun A => fderiv ℝ F A (d i)))) atTop (nhds 0)
    simp_rw [matrixL2_toLp_dist_eq_sqrt]
    simpa [g] using (matrixSpatialTruncation_L2_errors n μ F hF hv (d i) (hD i)).2.sqrt
  apply isClosed_closure.mem_of_tendsto (hvalue_converges.prodMk_nhds hgradient_converges)
  apply Eventually.of_forall
  intro k
  exact subset_closure ⟨g k, hg k, hc k, (htruncatedValue_memLp k).coeFn_toLp, fun i => (htruncatedDerivative_memLp k i).coeFn_toLp⟩

#print axioms matrixGaussian_C1_pair_mem_H1Completion
end
end GinibrePoincare
