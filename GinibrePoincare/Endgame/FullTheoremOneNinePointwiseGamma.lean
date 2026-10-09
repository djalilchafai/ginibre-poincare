module
public import GinibrePoincare.Endgame.FullTheoremOneNine
public import GinibrePoincare.Analysis.GinibreFullGeneratorCoreIdentification
public import GinibrePoincare.Analysis.CorrespondenceOperatorUnrestrictedGamma

@[expose] public section

/-! # From the generator deficit to the pointwise Γ₂ integral

The compact smooth collision-free core lies in the symmetric generator graph.
Apply the graph-domain deficits first. The unrestricted integration-by-parts
identity identifies the integral of pointwise Γ₂ with the squared L² norm of
the pregenerator; the almost-everywhere representative lemma then identifies
this norm with the core generator value. This last bridge is needed to express
the second deficit in the paper's differential notation.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Both concrete Theorem 1.9 identities on the paper's literal smooth core,
with the second deficit expressed using actual pointwise Γ₂. -/
theorem fullTheoremOneNinePointwiseGamma {n : ℕ} (hn : 0<n)
    (f : Configuration n → ℝ) (hf : IsTheoremOneNineCore f) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n (ginibreFullCoreValue hn f hf) g ∧
      ginibreWeakEnergy n g - 2*ginibreL2Variance n hn (ginibreFullCoreValue hn f hf) =
        2*‖ginibreFullHolomorphicRemainder n hn (ginibreFullCoreValue hn f hf)‖^2 +
          4*modeTail (positiveHermiteModeMass hn
            (ginibreFullCenteredTransform n hn (ginibreFullCoreValue hn f hf))) ∧
      (∫ z, ginibrePointwiseGammaTwo n f z ∂ginibreMeasure n)-2*ginibreWeakEnergy n g =
        ‖ginibreFullCorePregenerator hn f hf+(2 : ℝ) •
          ginibreFullCenter n hn (ginibreFullCoreValue hn f hf)‖^2 +
          4*‖ginibreFullHolomorphicRemainder n hn (ginibreFullCoreValue hn f hf)‖^2 +
          8*modeTail (positiveHermiteModeMass hn
            (ginibreFullCenteredTransform n hn (ginibreFullCoreValue hn f hf))) := by
  obtain ⟨g, deficits⟩ := fullTheoremOneNine_named hn
    (ginibreFullCoreSymmetricValue hn f hf) (ginibreFullCoreSymmetricPregenerator hn f hf)
    (ginibreFullGenerator_core_graph hn f hf)
  have hcf : tsupport f⊆{z|CollisionFree z} := by
    intro z hz
    exact (collisionFree_iff_not_mem_collisionSet z).mpr (hf.2.2.1 hz)
  have hΓ := correspondenceOperator_integral_pointwiseGammaTwo_unrestricted hn f
    ⟨hf.1, hf.2.1, hcf⟩
  have hi : (∫ z, (ginibrePregenerator n f z)^2 ∂ginibreMeasure n) =
      ‖ginibreFullCorePregenerator hn f hf‖^2 := by
    rw [← integral_square_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [ginibreFullCorePregenerator_ae hn f hf] with z hz
    rw [hz]
  refine ⟨g, deficits.distributional_gradient, deficits.poincare_deficit, ?_⟩
  rw [hΓ, hi]
  exact deficits.generator_deficit

#print axioms fullTheoremOneNinePointwiseGamma
end
end GinibrePoincare
