module

public import GinibrePoincare.Analysis.GinibreRadialPhaseMollification
public import GinibrePoincare.Analysis.RadialSobolevSpace

@[expose] public section

/-! # Radial core approximation and sharp LSI through collisions

Compact radial symmetric weak values on the phase-regular set admit actual
radial smooth core approximation. Gradient support is derived automatically.
-/

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Actual normalized radial convolutions give core approximants for weak pairs
with compact supports on the phase-regular set, including collisions and a single zero coordinate. -/
theorem radial_phaseRegular_weak_exists_core_sequence (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | PhaseRegular n z}) (hhs : tsupport h ⊆ {z | PhaseRegular n z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) := by
  obtain ⟨v, w, he, ht⟩ := ginibre_weighted_radial_phaseRegular_mollification
    n hn u g hg f h hf hh hfc hhc hfs hhs hr
  have fv := ginibre_radial_value_memLp_volume_phaseRegular n hn u f hf hr hfc hfs
  refine ⟨fun m => (v m, w m), ?_, ht⟩
  intro m
  exact ⟨radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f,
    radialMollifierKernel_convolution_core n m f fv hfc hs hr,
    (he m).2.2.1, (he m).2.2.2⟩

/-- Compact radial symmetric weak values supported on the phase-regular set
belong to the original radial smooth-core completion; collisions are allowed. -/
theorem radial_compact_phaseRegular_weak_mem_sobolevClosure
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hfs : tsupport f ⊆ {z | PhaseRegular n z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    (u, g) ∈ radialSobolevClosure n := by
  obtain ⟨h, hh, hhc, hhs⟩ := ginibre_distributional_gradient_exists_supported_representative
    n hn u g hg f hf hc
  obtain ⟨q, hq, ht⟩ := radial_phaseRegular_weak_exists_core_sequence n hn u g hg f h hf hh
    hc hhc hfs (hhs.trans hfs) hs hr
  apply isClosed_closure.mem_of_tendsto ht
  exact Eventually.of_forall (fun m => subset_closure (hq m))

/-- The sharp LSI follows for this independently weak class without a supplied
entropy, smoothness or gradient-support premise. -/
theorem radial_compact_phaseRegular_weak_lsi
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hfs : tsupport f ⊆ {z | PhaseRegular n z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g)
    (radial_compact_phaseRegular_weak_mem_sobolevClosure n hn u g hg f hf hc hfs hs hr)

/-- Core sequences exist without a supplied compact gradient representative. -/
theorem radial_compact_phaseRegular_weak_exists_core_sequence
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hc : HasCompactSupport f) (hfs : tsupport f ⊆ {z | PhaseRegular n z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) :=
  mem_closure_iff_seq_limit.mp
    (radial_compact_phaseRegular_weak_mem_sobolevClosure n hn u g hg f hf hc hfs hs hr)

end
end GinibrePoincare
