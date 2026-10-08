module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsLSIDriverIdentification
public import GinibrePoincare.Analysis.GinibreHamiltonianCompletedProductBrownian
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω]
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- Actual normalized strongly convex Gibbs LSI via the constructed Langevin
flow and internally proved Gibbs invariance. Brownian existence remains an
explicit process input in this stochastic theorem. -/
theorem bakryEmeryConfigurationGibbs_square_lsi_of_Brownian
    (n : ℕ) (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (B : (Fin n×Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : EuclideanSpace ℝ (Fin n×Fin 2) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm)) f ≤
      (2/κ)*∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (W ∘ (configurationEuclideanEquiv n).symm) := by
  let μ := bakryEmeryNormalizedGibbs volume W
  let ν := bakryEmeryNormalizedGibbs volume (W ∘ (configurationEuclideanEquiv n).symm)
  haveI : IsProbabilityMeasure μ := bakryEmeryConfiguration_gibbs_probability n W κ hκ hW hc
  let Q := (μ.prod P).completion
  let Ωc := NullMeasurableSpace (Configuration n×Ω) (μ.prod P)
  haveI : IsProbabilityMeasure Q := ginibre_completion_isProbabilityMeasure (μ.prod P)
  haveI : Nonempty (Fin n×Fin 2) := ⟨(⟨0,hn⟩,0)⟩
  let Bc : (Fin n×Fin 2) → ℝ≥0 → Ωc → ℝ := fun i t p => B i t p.2
  let Z : Ωc → EuclideanSpace ℝ (Fin n×Fin 2) := fun p => configurationEuclideanEquiv n p.1
  have hBc : ∀ i, IsBrownianReal (Bc i) Q :=
    ginibreBrownian_completed_initial_noise_product μ P B hB
  have hiBc : iIndepFun (fun i p t => Bc i t p) Q :=
    ginibreBrownian_completed_product_independent_coordinates μ P B hB hind
  apply bakryEmeryBrownianEndpoint_stationary_square_lsi
    (W ∘ (configurationEuclideanEquiv n).symm) κ hκ
    (hW.comp (configurationEuclideanEquiv n).symm.contDiff) hc 0 Z Bc Q hBc hiBc ν ?_ f hf hs
  intro m
  let T : ℝ≥0 := ⟨m+1,by positivity⟩
  let E : Configuration n×Ω → EuclideanSpace ℝ (Fin n×Fin 2) :=
    fun p => configurationEuclideanEquiv n (bakryEmeryGibbsActualEndpoint W hW κ hκ hc T B p)
  have hE : Measurable E := (configurationEuclideanEquiv n).continuous.measurable.comp
    (bakryEmeryGibbsActualEndpoint_measurable W hW κ hκ hc T B P hB)
  have hLaw : HasLaw (fun p : Ωc => E p) ν Q := by
    refine ⟨hE.nullMeasurable.measurable'.aemeasurable,?_⟩
    rw [ginibre_map_completion (μ.prod P) E hE]
    exact bakryEmeryGibbsActualEndpoint_hilbert_stationary hn W hW κ hκ hc P B hB hind T (by change (0 : ℝ) < (m:ℝ)+1; positivity)
  apply hLaw.congr
  have hAE := (ginibreCompletedProduct_snd_preserving μ P).quasiMeasurePreserving.ae
    (bakryEmeryGibbsActualEndpoint_eq_BrownianEndpoint n hn W hW κ hκ hc B P hB T)
  filter_upwards [hAE] with p hp
  exact (hp p.1).symm

#print axioms bakryEmeryConfigurationGibbs_square_lsi_of_Brownian
end
end GinibrePoincare
