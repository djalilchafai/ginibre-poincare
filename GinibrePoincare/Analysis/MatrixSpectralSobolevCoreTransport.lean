module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevDensityTransport
public import GinibrePoincare.Analysis.MatrixSpectralSobolevDirections

@[expose] public section

/-! # Genuine transport into the actual Gaussian matrix Sobolev completion

The measure-preserving entry equivalence induces an L² transport of values and
of every coordinate derivative. On compact smooth functions the chain rule
identifies the transported entry direction with the corresponding real matrix
direction; compact support is preserved by the homeomorphism. The resulting map
on value/gradient pairs is continuous. Its preimage of the closed matrix H¹
completion therefore contains the entire entry-coordinate core closure.
-/
open MeasureTheory Matrix Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

def matrixEntryMeasurableEquiv {n m : ℕ} (e : Fin m ≃ Fin n × Fin n) :
    Configuration m ≃ᵐ MatrixRealSpace n :=
  (matrixComplexEntryEquiv e).toHomeomorph.toMeasurableEquiv

def matrixEntryL2ToMatrix {n m : ℕ} (hn : 0 < n) (e : Fin m ≃ Fin n × Fin n) :
    Lp ℝ 2 (matrixEntryGaussianMeasure e) →L[ℝ] Lp ℝ 2 (matrixGaussianMeasure n) :=
  (Lp.compMeasurePreservingₗᵢ ℝ (matrixEntryMeasurableEquiv e).symm
    ((matrixComplexEntryEquiv_gaussian_preserving hn e).symm (matrixEntryMeasurableEquiv e))).toContinuousLinearMap

theorem matrixEntryL2ToMatrix_ae {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n) (u : Lp ℝ 2 (matrixEntryGaussianMeasure e)) :
    (matrixEntryL2ToMatrix hn e u : MatrixRealSpace n → ℝ) =ᵐ[matrixGaussianMeasure n]
      (fun A => u ((matrixComplexEntryEquiv e).symm A)) :=
  Lp.coeFn_compMeasurePreserving _ _

theorem matrixComplexEntryEquiv_symm_direction {n m : ℕ}
    (e : Fin m ≃ Fin n × Fin n) (i : MatrixRealIndex n) :
    (matrixComplexEntryEquiv e).symm (matrixRealCoordinates n (Pi.single i 1)) =
      ginibreCoordinateDirection ((matrixEntryRealIndexEquiv e).symm i) := by
  apply (matrixComplexEntryEquiv e).injective
  simpa only [ContinuousLinearEquiv.apply_symm_apply, Equiv.apply_symm_apply] using
    (matrixComplexEntryEquiv_direction e ((matrixEntryRealIndexEquiv e).symm i)).symm

/-- The actual compact smooth weighted entry-coordinate graph maps into the
actual matrix graph completion under the genuine Gaussian L² transport. -/
theorem matrixEntry_core_closure_transport {n m : ℕ} (hn : 0 < n)
    (e : Fin m ≃ Fin n × Fin n)
    (p : Lp ℝ 2 (matrixEntryGaussianMeasure e) ×
      ((Fin m × Fin 2) → Lp ℝ 2 (matrixEntryGaussianMeasure e)))
    (hp : p ∈ closure (weightedConfigurationCompactDirectionalPairs m (Fin m × Fin 2)
      ginibreCoordinateDirection (matrixEntryGaussianMeasure e))) :
    (matrixEntryL2ToMatrix hn e p.1,
      fun i => matrixEntryL2ToMatrix hn e (p.2 ((matrixEntryRealIndexEquiv e).symm i))) ∈
      matrixGaussianH1Completion n := by
  let T := matrixEntryL2ToMatrix hn e
  let Φ := fun q : Lp ℝ 2 (matrixEntryGaussianMeasure e) ×
      ((Fin m × Fin 2) → Lp ℝ 2 (matrixEntryGaussianMeasure e)) =>
    (T q.1, fun i => T (q.2 ((matrixEntryRealIndexEquiv e).symm i)))
  have hΦ : Continuous Φ := (T.continuous.comp continuous_fst).prodMk (continuous_pi fun i =>
    T.continuous.comp ((continuous_apply ((matrixEntryRealIndexEquiv e).symm i)).comp continuous_snd))
  have hpres := (matrixComplexEntryEquiv_gaussian_preserving hn e).symm (matrixEntryMeasurableEquiv e)
  have hsub : weightedConfigurationCompactDirectionalPairs m (Fin m × Fin 2)
      ginibreCoordinateDirection (matrixEntryGaussianMeasure e) ⊆
      Φ ⁻¹' matrixGaussianH1Completion n := by
    intro q hq
    obtain ⟨f, hf, hc, hv, hd⟩ := hq
    apply subset_closure
    let F := f ∘ (matrixComplexEntryEquiv e).symm
    have hF : ContDiff ℝ 1 F := hf.comp (matrixComplexEntryEquiv e).symm.contDiff
    have hFc : HasCompactSupport F := hc.comp_homeomorph (matrixComplexEntryEquiv e).symm.toHomeomorph
    refine ⟨F, hF, hFc, ?_, ?_⟩
    · filter_upwards [matrixEntryL2ToMatrix_ae hn e q.1,
        hpres.quasiMeasurePreserving.ae hv] with A hA hB
      exact hA.trans hB
    · intro i
      filter_upwards [matrixEntryL2ToMatrix_ae hn e (q.2 ((matrixEntryRealIndexEquiv e).symm i)),
        hpres.quasiMeasurePreserving.ae (hd ((matrixEntryRealIndexEquiv e).symm i))] with A hA hB
      change (q.2 ((matrixEntryRealIndexEquiv e).symm i)) ((matrixComplexEntryEquiv e).symm A) =
        fderiv ℝ f ((matrixComplexEntryEquiv e).symm A)
          (ginibreCoordinateDirection ((matrixEntryRealIndexEquiv e).symm i)) at hB
      rw [hA, hB]
      have hder := (hf.differentiable one_ne_zero ((matrixComplexEntryEquiv e).symm A)).hasFDerivAt.comp (show MatrixRealSpace n from A)
        (matrixComplexEntryEquiv e).symm.hasFDerivAt
      rw [show F = f ∘ (matrixComplexEntryEquiv e).symm from rfl, hder.fderiv]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
      rw [matrixComplexEntryEquiv_symm_direction]
  exact closure_minimal hsub (isClosed_closure.preimage hΦ) hp

end
end GinibrePoincare
