module

public import GinibrePoincare.Analysis.GinibreWeightedRadialInteriorMollification
public import GinibrePoincare.Analysis.RadialSobolevSpace

@[expose] public section

/-! # Smooth radial core approximation of interior weak-Sobolev pairs

Actual weak functions with compact radial symmetric representatives, and compact
weak-gradient representatives, supported away from collisions admit simultaneous
weighted smooth radial core approximation. This proves reverse inclusion and the
sharp LSI for that interior class, without assuming the initial value smooth.
-/

open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

variable (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ)
    (h : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hh : (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n] h)
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h)
    (hfs : tsupport f ⊆ {z | CollisionFree z}) (hhs : tsupport h ⊆ {z | CollisionFree z})
    (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))

include hn u g hg hf hh hfc hhc hfs hhs hs hr

/-- Concrete normalized radial convolutions give genuine core pairs approaching
the actual weak value and gradient simultaneously in Ginibre L². -/
theorem radial_interior_weak_exists_core_sequence :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) := by
  obtain ⟨v, w, he, ht⟩ := ginibre_weighted_radial_interior_mollification
    n hn u g hg f h hf hh hfc hhc hfs hhs
  have fv : MemLp f 2 volume := ginibre_memLp_volume_of_interior_compactSupport hn f
    ((memLp_congr_ae hf).mp (Lp.memLp u)) hfc hfs
  refine ⟨fun m => (v m, w m), ?_, ht⟩
  intro m
  exact ⟨radialMollifierKernel n m ⋆[lsmul ℝ ℝ, volume] f,
    radialMollifierKernel_convolution_core n m f fv hfc hs hr,
    (he m).2.2.1, (he m).2.2.2⟩

/-- Reverse inclusion is established for the interior compact weak radial class. -/
theorem radial_interior_weak_mem_sobolevClosure : (u, g) ∈ radialSobolevClosure n := by
  obtain ⟨q, hq, ht⟩ := radial_interior_weak_exists_core_sequence
    n hn u g hg f h hf hh hfc hhc hfs hhs hs hr
  apply isClosed_closure.mem_of_tendsto ht
  exact Eventually.of_forall (fun m => subset_closure (hq m))

/-- The sharp LSI and logarithmic integrability follow for this independently weak
interior radial class, without an initial smoothness or entropy premise. -/
theorem radial_interior_weak_lsi :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g)
    (radial_interior_weak_mem_sobolevClosure n hn u g hg f h hf hh hfc hhc hfs hhs hs hr)

end
end GinibrePoincare
