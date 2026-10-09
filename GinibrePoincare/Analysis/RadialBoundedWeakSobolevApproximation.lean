module

public import GinibrePoincare.Analysis.GinibreZeroPairL2Approximation
public import GinibrePoincare.Analysis.RadialPhaseWeakSobolevApproximation

@[expose] public section

/-! # Core approximation of bounded compact radial weak Sobolev values

The value support may meet simultaneous coordinate zeroes. Actual zero-pair
cutoffs reduce to the phase-regular theorem and converge in the full graph norm.
-/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Bounded compact radial symmetric weak pairs belong to the original radial
smooth-core completion, without any restriction on their value support. -/
theorem radial_bounded_compact_weak_mem_sobolevClosure
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    (u, g) ∈ radialSobolevClosure n := by
  have hfm : AEStronglyMeasurable f (ginibreMeasure n) := (Lp.aestronglyMeasurable u).congr hf
  let χ := ginibreZeroPairAvoidanceCutoff n
  let v (m : ℕ) := (ginibreZeroPair_mul_memLp n m u (Lp.memLp u)).toLp
    (fun z => χ m z • u z)
  let a (m : ℕ) := (ginibreZeroPair_mul_memLp n m g (Lp.memLp g)).toLp
    (fun z => χ m z • g z)
  let b (m : ℕ) := (ginibreZeroPairAvoidanceCutoff_bounded_gradient_memLp
    n hn f hfm hc A hA0 hA m).toLp
    (fun z => f z • ginibreEuclideanGradient (χ m) z)
  have hv (m : ℕ) : (v m : Configuration n → ℝ) =ᵐ[ginibreMeasure n]
      fun z => χ m z * u z := by
    simpa only [v, χ, smul_eq_mul] using
      (ginibreZeroPair_mul_memLp n m u (Lp.memLp u)).coeFn_toLp
  have hab (m : ℕ) : ((a m + b m : Lp (EuclideanSpace ℝ (Fin n × Fin 2))
      2 (ginibreMeasure n)) : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      =ᵐ[ginibreMeasure n] fun z => χ m z • g z + u z • ginibreEuclideanGradient (χ m) z := by
    filter_upwards [Lp.coeFn_add (a m) (b m),
      (ginibreZeroPair_mul_memLp n m g (Lp.memLp g)).coeFn_toLp,
      (ginibreZeroPairAvoidanceCutoff_bounded_gradient_memLp n hn f hfm hc A hA0 hA m).coeFn_toLp,
      hf] with z hz ha hb huf
    rw [hz]
    change a m z + b m z = _
    change a m z = _ at ha
    change b m z = _ at hb
    rw [ha, hb, huf]
  have hp (m : ℕ) : (v m, a m + b m) ∈ radialSobolevClosure n := by
    have hd := ginibre_distributional_gradient_mul n hn u g hg (χ m)
      (ginibreZeroPairAvoidanceCutoff_smooth n m) (v m) (a m + b m) (hv m) (hab m)
    apply radial_compact_phaseRegular_weak_mem_sobolevClosure n hn (v m) (a m + b m)
      hd ((χ m) * f)
    · apply (hv m).trans
      filter_upwards [hf] with z hz
      simp only [hz, Pi.mul_apply]
    · exact hc.mul_left
    · exact tsupport_mul_subset_left.trans
        (ginibreZeroPairAvoidanceCutoff_support_phaseRegular n hn m)
    · intro σ z
      simp only [Pi.mul_apply, ginibreZeroPairAvoidanceCutoff_symmetric n m σ z, hs σ z, χ]
    · obtain ⟨F, hF⟩ := hr
      obtain ⟨H, hH⟩ := ginibreZeroPairAvoidanceCutoff_radial n m
      exact ⟨fun r => H r * F r, fun z => by simp only [Pi.mul_apply, χ, hH, hF]⟩
  have ht : Tendsto (fun m => (v m, a m + b m)) atTop (𝓝 (u, g)) := by
    have hv' : Tendsto v atTop (𝓝 u) := ginibreZeroPair_mul_L2_tendsto n hn u
    have ha' : Tendsto a atTop (𝓝 g) := ginibreZeroPair_mul_L2_tendsto n hn g
    have hb' : Tendsto b atTop (𝓝 0) :=
      ginibreZeroPair_gradient_L2_tendsto n hn f hfm hc A hA0 hA
    exact hv'.prodMk_nhds (by simpa using ha'.add hb')
  exact isClosed_closure.mem_of_tendsto ht (Eventually.of_forall hp)

/-- Sharp LSI and entropy integrability for bounded compact independent radial
weak pairs, including values supported at simultaneous coordinate zeroes. -/
theorem radial_bounded_compact_weak_lsi
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g)
    (radial_bounded_compact_weak_mem_sobolevClosure n hn u g hg f hf hc hs hr A hA0 hA)

/-- Actual radial smooth core sequences approximate the full weak value-gradient
pair of a bounded compact radial symmetric value. -/
theorem radial_bounded_compact_weak_exists_core_sequence
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) :=
  mem_closure_iff_seq_limit.mp
    (radial_bounded_compact_weak_mem_sobolevClosure n hn u g hg f hf hc hs hr A hA0 hA)

/-- Bounded radial symmetric weak pairs have reverse core approximation without
compact support or any restriction excluding simultaneous coordinate zeroes. -/
theorem radial_bounded_weak_mem_sobolevClosure
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    (u, g) ∈ radialSobolevClosure n := by
  have hmem (m : ℕ) : ginibreWeakSpatialTruncation n hn u g m ∈ radialSobolevClosure n := by
    let q := ginibreWeakSpatialTruncation n hn u g m
    let f' := (ginibreSpatialCutoff n m) * f
    have he : (q.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f' := by
      apply (ginibreWeakSpatialTruncation_value_ae n hn u g m).trans
      filter_upwards [hf] with z hz
      simp only [f', hz, Pi.mul_apply]
    have hs' : IsSymmetric f' := by
      intro σ z
      simp only [f', Pi.mul_apply, ginibreSpatialCutoff_symmetric n m σ z, hs σ z]
    obtain ⟨F, hF⟩ := hr
    have hr' : ∃ G : (Fin n → ℝ) → ℝ, ∀ z, f' z = G (fun i => Complex.normSq (z i)) := by
      refine ⟨fun r => sobolevCutoff m (∑ i, r i) * F r, ?_⟩
      intro z
      simp only [f', Pi.mul_apply, hF, ginibreSpatialCutoff, configurationNormSq]
    apply radial_bounded_compact_weak_mem_sobolevClosure n hn q.1 q.2
      (ginibreWeakSpatialTruncation_distributional n hn u g hg m) f' he
      (ginibreSpatialCutoff_compact n m).mul_right hs' hr' A hA0
    intro z
    change ‖ginibreSpatialCutoff n m z * f z‖ ≤ A
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (ginibreSpatialCutoff_mem_unit n m z).1]
    exact (mul_le_of_le_one_left (norm_nonneg _) (ginibreSpatialCutoff_mem_unit n m z).2).trans (hA z)
  exact isClosed_closure.mem_of_tendsto (ginibreWeakSpatialTruncation_tendsto n hn u g)
    (Eventually.of_forall hmem)

/-- Sharp LSI and entropy integrability for bounded independent radial weak pairs
on the whole configuration space, without compact support. -/
theorem radial_bounded_weak_lsi
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g)
    (radial_bounded_weak_mem_sobolevClosure n hn u g hg f hf hs hr A hA0 hA)

/-- Actual core sequences converge simultaneously to the value and actual weak
gradient for bounded radial symmetric values, even without compact support. -/
theorem radial_bounded_weak_exists_core_sequence
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (A : ℝ) (hA0 : 0 ≤ A) (hA : ∀ z, ‖f z‖ ≤ A) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) :=
  mem_closure_iff_seq_limit.mp
    (radial_bounded_weak_mem_sobolevClosure n hn u g hg f hf hs hr A hA0 hA)
end
end GinibrePoincare
