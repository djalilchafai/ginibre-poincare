module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUSublevelInteractionDensity
public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltVolterra

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

/-- The actual selected OU interaction likelihood simultaneously normalizes,
turns the entire corrected driver into Brownian noise, and identifies its
reference path with the genuine canonical original Ginibre solution before
the actual positive stopping time. -/
theorem ginibreActualOU_sublevel_tilted_canonical_prefix_exists {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0<n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z<R) (T : ℝ≥0) (hT : 0<T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, CollisionFree (Y t ω)) ∧
      (∀ ω, Y 0 ω=z) ∧ ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0<θ ω ∧ θ ω≤T) ∧
      (∀ t ω, Y t ω=ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω) ∧
      (∀ ω, θ ω=ginibreHamiltonianOUSublevelStop n α z B R T ω) ∧
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i t, t≤T → TendstoInMeasure P (fun k => brownianUniformLeftSum (B i)
        (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (k+1)) atTop (M i t)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω))
      Q.map (fun ω (t : Icc (0 : ℝ≥0) T) i => ginibreInteractionCorrectedBrownian n α B Y i t.val ω)=
        P.map (fun ω (t : Icc (0 : ℝ≥0) T) i => B i t.val ω-B i 0 ω) ∧
      (∀ᵐ ω ∂Q, ∀ t : ℝ≥0, t≤θ ω → ginibreDrivenMaximalValue n α
        (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z t=Y t ω) ∧
      ∀ᵐ ω ∂Q, ∀ t≤θ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) t (fun i => M i t) ω =
        Real.exp (ginibreInteractionPotential n z)*
          (ginibreHamiltonianGradientPathWeight n α t (fun s => Y s.toNNReal ω)/
            ginibreQuadraticGradientPathWeight n α t (fun s => Y s.toNNReal ω)) := by
  classical
  obtain ⟨K, hK, hCF, Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hθActual, hEq, M, hM, hDi, hD1, hAction⟩ :=
    ginibreHamiltonianOU_sublevel_interaction_action_density_exists hn B P hB hind α z hz R hR T hT
  let F := fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i
  let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity F T (fun i => M i T) ω))
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  obtain ⟨C, hC, hb⟩ := ginibreInteractionBrownianTilt_compact_bound n α K hK hCF
  have hF (i : Fin n × Fin 2) (r : ℝ≥0) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r) :=
    (ginibreInteractionBrownianTilt_measurable n α i).comp (hY r).measurable
  have hFc (i : Fin n × Fin 2) : ∀ᵐ ω ∂P, ContinuousOn (fun r => F i r ω) (Icc 0 T) :=
    ae_of_all P (fun ω => ((ginibreInteractionBrownianTilt_continuousOn n α i).comp_continuous
      (hYC ω) (fun r => hCF _ (hYR r ω))).continuousOn)
  have hFi (i : Fin n × Fin 2) (r : ℝ≥0) : MemLp (F i r) 2 P := by
    apply MemLp.of_bound ((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable C
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    apply abs_le_of_sq_le_sq _ hC
    exact (Finset.single_le_sum (fun j _ => sq_nonneg (F j r ω)) (Finset.mem_univ i)).trans (hb _ (hYR r ω))
  have hLaw := brownianVectorExponentialIntegralDensity_whole_path_law B P hB hind F hF C hC
    (fun r ω => hb _ (hYR r ω)) T hT hFc
    (fun i k => (brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
      hind i (F i) (hF i) (hFi i) T (k+1)).aestronglyMeasurable)
    (fun i => M i T) (fun i => (hM i).2.2.2.2 T le_rfl)
  refine ⟨Y, hYC, fun r ω => hCF _ (hYR r ω), hY0, θ, hStop, hθ, hStopped, hθActual, M,
    fun i t ht => (hM i).2.2.2.2 t ht, hDi, hD1, hLaw.2.2.1,?_, hQP.ae_le hAction⟩
  apply hQP.ae_le
  have hBcont := ae_all_iff.mpr (fun i => (hB i).cont)
  filter_upwards [hEq, ginibreConfigurationBrownianNoise_actual n B P hB α, hBcont] with ω hEqω hNω hBω
  let y := fun s : ℝ => Y s.toNNReal ω
  let N := ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω
  have hVol := ginibreOUPath_correctedBrownian_original_volterra n α α.property B Y ω z (θ ω)
    (hYC ω) (fun t => hCF _ (hYR t ω)) hNω.2 hEqω
  have hD : Continuous (fun s : ℝ => ginibreLangevinDrift n α (y s)) := by
    apply continuous_iff_continuousAt.mpr
    intro s
    exact (ginibreLangevinDrift_contDiffAt n α (y s) (hCF _ (hYR _ ω))).continuousAt.comp
      ((hYC ω).comp continuous_real_toNNReal).continuousAt
  have hseg : GinibreDrivenSegment n α N z (θ ω) y := by
    refine ⟨((hYC ω).comp continuous_real_toNNReal).continuousOn,?_,?_⟩
    · simpa only [y, Real.toNNReal_zero] using hY0 ω
    · intro s hs
      refine ⟨hCF _ (hYR _ ω), hD.intervalIntegrable 0 s,?_⟩
      have he := hVol s.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hs.2)
      simpa only [y, N, Real.coe_toNNReal _ hs.1] using he
  have hN := ginibreInteractionCorrectedBrownian_noise_continuous n α B Y ω hBω (hYC ω) (fun t => hCF _ (hYR t ω))
  have hL := hseg.horizon_lt_lifetime hN.1 hN.2
  intro t ht
  simpa only [y, N, Real.toNNReal_coe] using
    ginibreDrivenMaximalValue_eq_segment hseg t ht ((ENNReal.coe_le_coe.mpr ht).trans_lt hL)

end
end GinibrePoincare
