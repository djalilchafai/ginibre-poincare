module

public import GinibrePoincare.Analysis.GinibreWeakSobolevMultipliers
public import GinibrePoincare.Analysis.GinibreDirectionalCoordinates
public import GinibrePoincare.Analysis.RadialConvolutionInvariance

@[expose] public section

/-! # Real-linear phase coordinates and local Lebesgue transport -/

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 400000

/-- Independent coordinate multiplication as an actual real-linear map. -/
def coordinatePhaseCLM (n : ℕ) (a : Fin n → ℂ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun i => a i • ContinuousLinearMap.proj i

@[simp] theorem coordinatePhaseCLM_apply (n : ℕ) (a : Fin n → ℂ) (z : Configuration n) :
    coordinatePhaseCLM n a z = coordinatePhase a z := by
  rfl

/-- Unit phases give a continuous real-linear equivalence. -/
def coordinatePhaseCLE (n : ℕ) (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    Configuration n ≃L[ℝ] Configuration n :=
  ContinuousLinearEquiv.equivOfInverse (coordinatePhaseCLM n a)
    (coordinatePhaseCLM n (fun i => (a i)⁻¹))
    (by
      intro z
      ext i
      have hne : a i ≠ 0 := by intro he; simpa [he] using ha i
      simp [coordinatePhaseCLM, hne, mul_assoc])
    (by
      intro z
      ext i
      have hne : a i ≠ 0 := by intro he; simpa [he] using ha i
      simp [coordinatePhaseCLM, hne, mul_assoc])

@[simp] theorem coordinatePhaseCLE_apply (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ = 1) (z : Configuration n) :
    coordinatePhaseCLE n a ha z = coordinatePhase a z := rfl

theorem measurePreserving_coordinatePhaseCLE_volume (n : ℕ) (a : Fin n → ℂ)
    (ha : ∀ i, ‖a i‖ = 1) :
    MeasurePreserving (coordinatePhaseCLE n a ha)
      (volume : Measure (Configuration n)) volume :=
  measurePreserving_coordinatePhase_volume n a ha

/-- Local Lebesgue integrability is transported through an actual volume-preserving
real-linear equivalence onto the preimage open set. -/
theorem locallyIntegrableOn_comp_volume_equiv (n : ℕ)
    {V : Type*} [NormedAddCommGroup V]
    (e : Configuration n ≃L[ℝ] Configuration n)
    (he : MeasurePreserving e (volume : Measure (Configuration n)) volume)
    (U : Set (Configuration n)) (hU : IsOpen U) (f : Configuration n → V)
    (hf : LocallyIntegrableOn f U volume) :
    LocallyIntegrableOn (f ∘ e) (e ⁻¹' U) volume := by
  apply (locallyIntegrableOn_iff (hU.preimage e.continuous).isLocallyClosed).mpr
  intro K hK hc
  have hi : IntegrableOn f (e '' K) volume := hf.integrableOn_compact_subset
    (by rintro _ ⟨x, hx, rfl⟩; exact hK hx) (hc.image e.continuous)
  exact (he.integrableOn_image e.toHomeomorph.toMeasurableEquiv.measurableEmbedding).mp hi

/-- A radial L² value is invariant a.e. under every fixed unit phase rotation,
with Lebesgue a.e. equality independent of the weighted density. -/
theorem ginibre_radial_L2_phase_ae (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (a : Fin n → ℂ) (ha : ∀ i, ‖a i‖ = 1) :
    ∀ᵐ z ∂(volume : Measure (Configuration n)), u (coordinatePhase a z) = u z := by
  have hf' := (ginibre_ae_eq_iff_volume n hn _ _).mp hf
  have he := (measurePreserving_coordinatePhaseCLE_volume n a ha).quasiMeasurePreserving.ae_eq_comp hf'
  filter_upwards [hf', he] with z hz hz'
  exact hz'.trans ((radial_coordinatePhase hr a ha z).trans hz.symm)

end
end GinibrePoincare
