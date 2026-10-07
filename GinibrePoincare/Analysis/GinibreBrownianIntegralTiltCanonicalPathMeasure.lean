module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltOUSublevelCanonicalLaw
public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltKilledMapping

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
local instance canonicalPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0:ℝ) (T:ℝ),Configuration n) := borel _
local instance canonicalPathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0:ℝ) (T:ℝ),Configuration n) := ⟨rfl⟩

def ginibreCanonicalCompactPath {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (T : ℝ≥0) (N : Ω → ℝ → Configuration n) : Ω → C(Icc (0:ℝ) (T:ℝ),Configuration n) :=
  ginibreFiniteContinuousNoiseNormalize n T
    (fun ω t => ginibreDrivenMaximalPath n α (N ω) z t.val)

theorem ginibreCanonicalCompactPath_apply_of_alive {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (T : ℝ≥0) (N : Ω → ℝ → Configuration n) (ω : Ω)
    (hAlive : (T:ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (N ω) z)
    (t : Icc (0:ℝ) (T:ℝ)) :
    ginibreCanonicalCompactPath n α z T N ω t=ginibreDrivenMaximalPath n α (N ω) z t.val := by
  have hc : Continuous (fun t : Icc (0:ℝ) (T:ℝ) => ginibreDrivenMaximalPath n α (N ω) z t.val) :=
    continuousOn_iff_continuous_domRestrict.mp (ginibreDrivenMaximalPath_segment T hAlive).1
  simp [ginibreCanonicalCompactPath,ginibreFiniteContinuousNoiseNormalize,ContinuousMap.mkD,hc]

theorem ginibreCanonicalCompactPath_forall_iff_of_alive {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (T : ℝ≥0) (N : Ω → ℝ → Configuration n) (ω : Ω)
    (hAlive : (T:ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (N ω) z)
    (A : Set (Configuration n)) :
    (∀ t, ginibreCanonicalCompactPath n α z T N ω t∈A) ↔
      (∀ t≤T, ginibreDrivenMaximalValue n α (N ω) z t∈A) := by
  constructor
  · intro h t ht
    have he := h (⟨t,⟨t.property,by exact_mod_cast ht⟩⟩ : Icc (0:ℝ) (T:ℝ))
    simpa only [ginibreCanonicalCompactPath_apply_of_alive n α z T N ω hAlive,
      ginibreDrivenMaximalPath,Real.toNNReal_coe] using he
  · intro h t
    rw [ginibreCanonicalCompactPath_apply_of_alive n α z T N ω hAlive]
    exact h t.val.toNNReal (Real.toNNReal_le_iff_le_coe.mpr t.property.2)

/-- Passing the actual canonical whole raw path law to a genuine continuous
compact-path probability measure. This mapping reduction uses the proved actual raw law and finite lifetimes; both
normalizations agree with the actual paths almost surely. -/
theorem ginibreActualCanonical_compact_path_law {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (nPos : 0<n) (α : ℝ) (z : Configuration n) (T : ℝ≥0)
    (P Q : Measure Ω) [P.IsComplete] (hQP : Q ≪ P) (hPQ : P ≪ Q)
    (N M : Ω → ℝ → Configuration n)
    (hAliveN : ∀ᵐ ω ∂Q, (T:ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (N ω) z)
    (hAliveM : ∀ᵐ ω ∂P, (T:ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (M ω) z)
    (hLaw : IdentDistrib
      (fun ω (t : Icc (0:ℝ≥0) T) => ginibreDrivenMaximalValue n α (N ω) z t.val)
      (fun ω (t : Icc (0:ℝ≥0) T) => ginibreDrivenMaximalValue n α (M ω) z t.val) Q P) :
    Measurable (ginibreCanonicalCompactPath n α z T N) ∧
      Measurable (ginibreCanonicalCompactPath n α z T M) ∧
      Q.map (ginibreCanonicalCompactPath n α z T N)=P.map (ginibreCanonicalCompactPath n α z T M) := by
  let R := fun f : Icc (0:ℝ≥0) T → Configuration n => fun t : Icc (0:ℝ) (T:ℝ) =>
    f ⟨t.val.toNNReal,⟨bot_le,Real.toNNReal_le_iff_le_coe.mpr t.property.2⟩⟩
  have hRm : Measurable R := by
    apply measurable_pi_lambda
    intro t
    exact measurable_pi_apply _
  have hReal := hLaw.comp hRm
  have hXm : Measurable (fun ω (t : Icc (0:ℝ) (T:ℝ)) => ginibreDrivenMaximalPath n α (N ω) z t.val) :=
    aemeasurable_iff_measurable.mp (hReal.aemeasurable_fst.mono_ac hPQ)
  have hYm : Measurable (fun ω (t : Icc (0:ℝ) (T:ℝ)) => ginibreDrivenMaximalPath n α (M ω) z t.val) :=
    aemeasurable_iff_measurable.mp hReal.aemeasurable_snd
  have hcNQ : ∀ᵐ ω ∂Q, Continuous (fun t : Icc (0:ℝ) (T:ℝ) => ginibreDrivenMaximalPath n α (N ω) z t.val) := by
    filter_upwards [hAliveN] with ω hω
    exact continuousOn_iff_continuous_domRestrict.mp (ginibreDrivenMaximalPath_segment T hω).1
  have hcNP : ∀ᵐ ω ∂P, Continuous (fun t : Icc (0:ℝ) (T:ℝ) => ginibreDrivenMaximalPath n α (N ω) z t.val) :=
    hPQ.ae_le hcNQ
  have hcM : ∀ᵐ ω ∂P, Continuous (fun t : Icc (0:ℝ) (T:ℝ) => ginibreDrivenMaximalPath n α (M ω) z t.val) := by
    filter_upwards [hAliveM] with ω hω
    exact continuousOn_iff_continuous_domRestrict.mp (ginibreDrivenMaximalPath_segment T hω).1
  exact ginibreFiniteContinuousNoiseNormalize_law n T P Q _ _ hXm hYm hcNP hcM hQP hReal.map_eq

/-! The following endpoint constructs the likelihood and whole canonical law internally. -/
theorem ginibreActualOU_sublevel_canonical_compact_path_law_exists {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0<n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ)
    (hR : ginibreHamiltonian n z<R) (T : ℝ≥0) (hT : 0<T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      ∃ M : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ,
      (∀ i, TendstoInMeasure P (fun k => brownianUniformLeftSum (B i)
        (fun r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (k+1)) atTop (M i T)) ∧
      Integrable (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T)) P ∧
      (∫ ω, brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω ∂P)=1 ∧
      let Q := P.withDensity (fun ω => ENNReal.ofReal (brownianVectorExponentialIntegralDensity
        (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω))
      ((∀ᵐ ω ∂Q, (T:ℝ≥0∞)<ginibreDrivenMaximalLifetime n α
        (ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω) z) ∧
      (Measurable (ginibreCanonicalCompactPath n α z T (fun ω =>
        ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω)) ∧
      Measurable (ginibreCanonicalCompactPath n α z T (fun ω =>
        (ginibreBrownianFullContinuousNoise n B α ω).val)) ∧
      Q.map (ginibreCanonicalCompactPath n α z T (fun ω =>
        ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω))=
      P.map (ginibreCanonicalCompactPath n α z T (fun ω =>
        (ginibreBrownianFullContinuousNoise n B α ω).val)))) ∧
      ∀ᵐ ω ∂Q,
        let N := ginibreConfigurationBrownianNoise n (ginibreInteractionCorrectedBrownian n α B Y) α ω
        ((∀ t≤T, ginibreDrivenMaximalValue n α N z t ∈ ginibreHamiltonianOUSublevelDomain n R) ↔
          (∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ ginibreHamiltonianOUSublevelDomain n R)) ∧
        ((∀ t≤T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ ginibreHamiltonianOUSublevelDomain n R) →
          (∀ t≤T, ginibreDrivenMaximalValue n α N z t=ginibreHamiltonianOUReferenceProcess n α z B t ω) ∧
          (∀ t≤T, Y t ω=ginibreHamiltonianOUReferenceProcess n α z B t ω) ∧
          brownianVectorExponentialIntegralDensity
            (fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i) T (fun i => M i T) ω =
            Real.exp (ginibreInteractionPotential n z)*
              (ginibreHamiltonianGradientPathWeight n α T (fun s => Y s.toNNReal ω)/
                ginibreQuadraticGradientPathWeight n α T (fun s => Y s.toNNReal ω))) := by
  obtain ⟨Y,M,hM,hDi,hD1,hPath,hCouple⟩ :=
    ginibreActualOU_sublevel_canonical_whole_path_law_exists hn B P hB hind α z hz R hR T hT
  let F := fun i r ω => ginibreInteractionBrownianTilt n α (Y r ω) i
  let D := brownianVectorExponentialIntegralDensity F T (fun i => M i T)
  let Q := P.withDensity (fun ω => ENNReal.ofReal (D ω))
  have hQP : Q ≪ P := withDensity_absolutelyContinuous P _
  have hPQ : P ≪ Q := withDensity_absolutelyContinuous'
    (ENNReal.measurable_ofReal.comp_aemeasurable hDi.aemeasurable)
    (ae_of_all P (fun ω => ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _))))
  have hAliveM : ∀ᵐ ω ∂P, (T:ℝ≥0∞)<ginibreDrivenMaximalLifetime n α
      (ginibreBrownianFullContinuousNoise n B α ω).val z := by
    filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω hω
    change (T:ℝ≥0∞)<ginibreBrownianMaximalLifetime n α z B ω
    rw [hω]
    exact ENNReal.coe_lt_top
  refine ⟨Y,M,hM,hDi,hD1,⟨hPath.1,?_⟩,hCouple⟩
  exact ginibreActualCanonical_compact_path_law hn α z T P Q hQP hPQ _ _ hPath.1 hAliveM hPath.2

#print axioms ginibreActualOU_sublevel_canonical_compact_path_law_exists

#print axioms ginibreActualCanonical_compact_path_law
end
end GinibrePoincare
