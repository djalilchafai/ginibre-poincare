module

public import GinibrePoincare.Analysis.RadialPhaseWeakSobolevApproximation
public import GinibrePoincare.Analysis.GinibreRadialWeakSobolevApproximation

@[expose] public section

/-! # Noncompact radial weak values supported on the phase-regular set

Spatial truncation removes the compactness premise from phase-regular weak
approximation. For one particle every configuration is phase regular, so reverse
core approximation and the sharp LSI hold for all independent radial weak pairs.
-/

open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Radial symmetric weak values whose support lies in the phase-regular set
belong to the smooth radial completion even without compact support. -/
theorem radial_phaseRegular_weak_mem_sobolevClosure
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hfs : tsupport f ⊆ {z | PhaseRegular n z}) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
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
    exact radial_compact_phaseRegular_weak_mem_sobolevClosure n hn q.1 q.2
      (ginibreWeakSpatialTruncation_distributional n hn u g hg m) f' he
      (ginibreSpatialCutoff_compact n m).mul_right
      (tsupport_mul_subset_right.trans hfs) hs' hr'
  exact isClosed_closure.mem_of_tendsto (ginibreWeakSpatialTruncation_tendsto n hn u g)
    (Eventually.of_forall hmem)

/-- The sharp LSI holds on this independent noncompact weak radial class. -/
theorem radial_phaseRegular_weak_lsi
    (n : ℕ) (hn : 0 < n) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hfs : tsupport f ⊆ {z | PhaseRegular n z}) (hs : IsSymmetric f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g)
    (radial_phaseRegular_weak_mem_sobolevClosure n hn u g hg f hf hfs hs hr)

/-- Every one-particle configuration is phase regular, including the origin. -/
theorem phaseRegular_one (z : Configuration 1) : PhaseRegular 1 z := by
  apply (phaseRegular_iff_zero_injective 1 (by norm_num) z).mpr
  intro i j _ _
  exact Subsingleton.elim i j

/-- Full reverse radial weak-to-core approximation for one particle, with no
support restriction or core-membership assumption. -/
theorem ginibreRadialWeakSobolevPairs_one_subset_sobolevClosure :
    ginibreRadialWeakSobolevPairs 1 ⊆ radialSobolevClosure 1 := by
  rintro p ⟨hg, f, hs, hr, hf⟩
  exact radial_phaseRegular_weak_mem_sobolevClosure 1 (by norm_num) p.1 p.2 hg f hf
    (fun z _ => phaseRegular_one z) hs hr

/-- Sharp LSI for every independently defined radial weak pair of the one-particle
Ginibre measure; no smoothness, support or entropy premise is required. -/
theorem ginibre_radial_weak_one_lsi
    (u : Lp ℝ 2 (ginibreMeasure 1))
    (g : Lp (EuclideanSpace ℝ (Fin 1 × Fin 2)) 2 (ginibreMeasure 1))
    (hg : IsGinibreDistributionalGradient 1 u g) (hr : IsGinibreRadialL2Value 1 u) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure 1) ∧
      ginibreSquareEntropy 1 u ≤ ‖g‖ ^ 2 := by
  simpa only [ginibreSquareEntropy, Nat.cast_one, div_one, one_mul] using radial_sobolev_lsi 1 (by norm_num) (u, g)
    (ginibreRadialWeakSobolevPairs_one_subset_sobolevClosure ⟨hg, hr⟩)

end
end GinibrePoincare
