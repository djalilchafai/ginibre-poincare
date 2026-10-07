module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevLocalIntegrability
public import GinibrePoincare.Analysis.MatrixSpectralSobolevWeightedCompact

@[expose] public section

/-! # Unconditional compact weak graph approximation for positive bounded densities -/
open MeasureTheory Filter
open scoped Topology ENNReal ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem positive_density_compact_weak_pair_mem_closure (m : ℕ)
    {I : Type*} [Fintype I] (v : I → Configuration m)
    (μ : Measure (Configuration m)) (w : Configuration m → ℝ)
    (hw : Continuous w) (hpos : ∀ x, 0 < w x)
    (hμ : μ = (volume : Measure (Configuration m)).withDensity (fun x => ENNReal.ofReal (w x)))
    (c : ℝ≥0∞) (hc : c ≠ (⊤ : ℝ≥0∞))
    (hbound : μ ≤ c • (volume : Measure (Configuration m)))
    (f : Configuration m → ℝ) (g : I → Configuration m → ℝ)
    (hf : MemLp f 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hfc : HasCompactSupport f) (hgc : ∀ i, HasCompactSupport (g i))
    (hweak : ∀ i, ∀ θ : Configuration m → ℝ,
      ContDiff ℝ ∞ θ → HasCompactSupport θ →
      (∫ x, g i x * θ x) = -(∫ x, f x * fderiv ℝ θ x (v i))) :
    (hf.toLp f, fun i => (hg i).toLp (g i)) ∈
      closure (weightedConfigurationCompactDirectionalPairs m I v μ) := by
  have hfv : MemLp f 2 volume :=
    positive_density_memLp_volume_of_compactSupport volume w hw hpos f
      (by rwa [← hμ]) hfc
  have hgv (i : I) : MemLp (g i) 2 volume :=
    positive_density_memLp_volume_of_compactSupport volume w hw hpos (g i)
      (by rw [← hμ]; exact hg i) (hgc i)
  exact weighted_configuration_compact_weak_pair_mem_closure m v μ c hc hbound
    f g hfv hgv hfc hgc hweak

end
end GinibrePoincare
