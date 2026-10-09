module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralTiltConfigurationLaw
public import GinibrePoincare.Analysis.GinibreStochasticNoncollision

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
local instance actualCanonicalFiniteMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance actualCanonicalFiniteBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

theorem ginibreActualNoise_prefix_alive_transfer {n : ℕ} (α : ℝ)
    (z : Configuration n) (T : ℝ≥0) (N M : ℝ → Configuration n)
    (hM : Continuous M) (hM0 : M 0=0) (hEq : EqOn M N (Icc 0 (T : ℝ)))
    (hAlive : (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α N z) :
    (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α M z ∧
      ∀ t≤T, ginibreDrivenMaximalValue n α M z t=ginibreDrivenMaximalValue n α N z t := by
  have hSeg := ginibreDrivenMaximalPath_segment T hAlive
  have hSegM : GinibreDrivenSegment n α M z T (ginibreDrivenMaximalPath n α N z) := by
    refine ⟨hSeg.1, hSeg.2.1,?_⟩
    intro s hs
    refine ⟨(hSeg.2.2 s hs).1, (hSeg.2.2 s hs).2.1,?_⟩
    rw [hEq hs]
    exact (hSeg.2.2 s hs).2.2
  have hAliveM := hSegM.horizon_lt_lifetime hM hM0
  refine ⟨hAliveM,?_⟩
  intro t ht
  simpa only [ginibreDrivenMaximalPath, Real.toNNReal_coe] using
    ginibreDrivenMaximalValue_eq_segment hSegM t ht ((ENNReal.coe_le_coe.mpr ht).trans_lt hAliveM)

/-- Mapping reduction removing finite-driver normalization: actual continuous
zero-initial noises with equal finite continuous laws give the same genuine
canonical original path law, provided the reference original solution is
alive. This also proves the tilted actual solution is alive on the horizon. -/
theorem ginibreActualFiniteNoise_canonical_whole_path_law {Ω : Type*}
    [MeasurableSpace Ω] {n : ℕ} (hn : 0<n) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (T : ℝ≥0)
    (P Q : Measure Ω) (N M : Ω → ℝ → Configuration n)
    (hN : ∀ᵐ ω ∂Q, Continuous (N ω) ∧ N ω 0=0)
    (hM : ∀ᵐ ω ∂P, Continuous (M ω) ∧ M ω 0=0)
    (hAliveM : ∀ᵐ ω ∂P, (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (M ω) z)
    (hXm : Measurable (ginibreFiniteContinuousNoiseNormalize n T (fun ω t => N ω t.val)))
    (hYm : Measurable (ginibreFiniteContinuousNoiseNormalize n T (fun ω t => M ω t.val)))
    (hLaw : Q.map (ginibreFiniteContinuousNoiseNormalize n T (fun ω t => N ω t.val))=
      P.map (ginibreFiniteContinuousNoiseNormalize n T (fun ω t => M ω t.val))) :
    (∀ᵐ ω ∂Q, (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (N ω) z) ∧
      IdentDistrib (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (N ω) z t.val)
        (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (M ω) z t.val) Q P := by
  let X := ginibreFiniteContinuousNoiseNormalize n T (fun ω t => N ω t.val)
  let Y := ginibreFiniteContinuousNoiseNormalize n T (fun ω t => M ω t.val)
  let E := fun f : C(Icc (0 : ℝ) (T : ℝ), Configuration n) => (ginibreFiniteNoiseExtension n T f).val
  have hFit (L : ℝ → Configuration n) (hLc : Continuous L) (hL0 : L 0=0) :
      EqOn (E (ContinuousMap.mkD (fun t : Icc (0 : ℝ) (T : ℝ) => L t.val) 0)) L (Icc 0 (T : ℝ)) := by
    intro s hs
    have hc : Continuous (fun t : Icc (0 : ℝ) (T : ℝ) => L t.val) := hLc.comp continuous_subtype_val
    simp [E, ginibreFiniteNoiseExtension_apply n T _ s hs, ContinuousMap.mkD, hc, hL0]
  have hYmAlive : ∀ᵐ ω ∂P, (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (E (Y ω)) z := by
    filter_upwards [hM, hAliveM] with ω hω hA
    exact (ginibreActualNoise_prefix_alive_transfer α z T (M ω) (E (Y ω))
      (ginibreFiniteNoiseExtension n T (Y ω)).val.continuous
      (ginibreFiniteNoiseExtension n T (Y ω)).property (hFit _ hω.1 hω.2) hA).1
  have hAliveMeas : MeasurableSet {f : C(Icc (0 : ℝ) (T : ℝ), Configuration n) |
      (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (E f) z} := by
    exact (ginibreDrivenMaximalLifetime_joint_alive_isOpen hn α T).measurableSet.preimage
      ((measurable_const (a := (⟨z, hz⟩ : {z : Configuration n // CollisionFree z}))).prodMk
        (ginibreFiniteNoiseExtension_measurable n T))
  have hXmAlive : ∀ᵐ ω ∂Q, (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (E (X ω)) z :=
    (show IdentDistrib X Y Q P from ⟨hXm.aemeasurable, hYm.aemeasurable, hLaw⟩).symm.ae_snd hAliveMeas hYmAlive
  have hEqN : ∀ᵐ ω ∂Q,
      (T : ℝ≥0∞)<ginibreDrivenMaximalLifetime n α (N ω) z ∧
      ∀ t≤T, ginibreDrivenMaximalValue n α (N ω) z t=ginibreDrivenMaximalValue n α (E (X ω)) z t := by
    filter_upwards [hN, hXmAlive] with ω hω hA
    exact ginibreActualNoise_prefix_alive_transfer α z T (E (X ω)) (N ω) hω.1 hω.2
      (fun s hs => (hFit _ hω.1 hω.2 hs).symm) hA
  have hEqM : ∀ᵐ ω ∂P, ∀ t≤T,
      ginibreDrivenMaximalValue n α (M ω) z t=ginibreDrivenMaximalValue n α (E (Y ω)) z t := by
    filter_upwards [hM, hYmAlive] with ω hω hA
    exact (ginibreActualNoise_prefix_alive_transfer α z T (E (Y ω)) (M ω) hω.1 hω.2
      (fun s hs => (hFit _ hω.1 hω.2 hs).symm) hA).2
  have hIdent := ginibreFiniteNoise_canonical_whole_path_identDistrib hn α z hz T Q P X Y hXm hYm hLaw
  have heN : (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (E (X ω)) z t.val)=ᵐ[Q]
      (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (N ω) z t.val) := by
    filter_upwards [hEqN] with ω hω
    funext t
    exact (hω.2 t.val t.property.2).symm
  have heM : (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (E (Y ω)) z t.val)=ᵐ[P]
      (fun ω (t : Icc (0 : ℝ≥0) T) => ginibreDrivenMaximalValue n α (M ω) z t.val) := by
    filter_upwards [hEqM] with ω hω
    funext t
    exact (hω t.val t.property.2).symm
  exact ⟨hEqN.mono (fun ω hω => hω.1), hIdent.aemeasurable_fst.congr heN,
    hIdent.aemeasurable_snd.congr heM,
    (Measure.map_congr heN).symm.trans (hIdent.map_eq.trans (Measure.map_congr heM))⟩

#print axioms ginibreActualFiniteNoise_canonical_whole_path_law
end
end GinibrePoincare
