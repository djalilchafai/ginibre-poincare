module

public import GinibrePoincare.Analysis.GinibrePhaseRegularSobolev
public import GinibrePoincare.Analysis.WeakTestLocalization

@[expose] public section

/-! # Radial ordinary weak derivatives through collisions

Phase patches cover every configuration with at most one zero coordinate. Their actual
weak test identities glue to identities on this whole open region, including
collisions. Neither the value nor the gradient is assumed to lie in a core closure.
-/

open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Local integrability of the norm squared implies local integrability of the
actual function, with no continuity premise on the function. -/
theorem locallyIntegrableOn_of_norm_sq (n : ℕ)
    {V : Type*} [NormedAddCommGroup V] (f : Configuration n → V)
    (U : Set (Configuration n)) (hm : AEStronglyMeasurable f volume)
    (hf : LocallyIntegrableOn (fun z => ‖f z‖ ^ 2) U volume) :
    LocallyIntegrableOn f U volume := by
  apply (hf.add (locallyIntegrableOn_const (1 : ℝ))).mono hm
  apply ae_of_all
  intro z
  change ‖f z‖ ≤ ‖‖f z‖ ^ 2 + 1‖
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  nlinarith [sq_nonneg (‖f z‖ - 1)]

/-- Radial values are locally Lebesgue integrable across collisions on the phase-regular set. -/
theorem ginibre_radial_value_locallyIntegrable_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    LocallyIntegrableOn (u : Configuration n → ℝ) {z | PhaseRegular n z} volume :=
  phase_invariant_locallyIntegrable_phaseRegular n u
    (ginibre_memLp_locallyIntegrable_collisionFree hn u (Lp.memLp u))
    (fun a ha => ginibre_radial_L2_phase_ae n hn u f hf hr a ha)

/-- The actual radial weak gradient is locally integrable on the same open region. -/
theorem ginibre_radial_gradient_locallyIntegrable_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    LocallyIntegrableOn (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2))
      {z | PhaseRegular n z} volume :=
  locallyIntegrableOn_of_norm_sq n g _
    (AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable g))
    (ginibre_radial_gradient_norm_sq_locallyIntegrable_phaseRegular n hn u g hg f hf hr)

/-- The original actual weak gradient satisfies every smooth compact coordinate
test on the phase-regular set, even when the test crosses collisions. -/
theorem ginibre_radial_weak_test_phaseRegular (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (k : Fin n × Fin 2) (θ : Configuration n → ℝ)
    (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hs : tsupport θ ⊆ {z | PhaseRegular n z}) :
    (∫ z, g z k * θ z) = -(∫ z, u z * fderiv ℝ θ z (ginibreCoordinateDirection k)) := by
  let U := {z : Configuration n | PhaseRegular n z}
  let A := {a : Fin n → ℂ // ∀ i, ‖a i‖ = 1}
  let V (a : A) := U ∩ (coordinatePhaseCLE n a.val a.property) ⁻¹' {z | CollisionFree z}
  have hU : IsOpen U := isOpen_phaseRegular n
  have hV (a : A) : IsOpen (V a) :=
    hU.inter ((isOpen_collisionFree n).preimage (coordinatePhaseCLE n a.val a.property).continuous)
  have hcover : U ⊆ ⋃ a : A, V a := by
    intro z hz
    obtain ⟨a, ha, hsep⟩ := hz
    exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, ⟨a, ha, hsep⟩, hsep⟩
  let P : EuclideanSpace ℝ (Fin n × Fin 2) →L[ℝ] ℝ :=
    PiLp.proj 2 (fun _ : Fin n × Fin 2 => ℝ) k
  have hw : LocallyIntegrableOn (fun z => g z k) U volume :=
    P.locallyIntegrableOn_comp
      (ginibre_radial_gradient_locallyIntegrable_phaseRegular n hn u g hg f hf hr)
  apply weak_derivative_test_of_open_cover n U hU u (fun z => g z k)
    (ginibre_radial_value_locallyIntegrable_phaseRegular n hn u f hf hr) hw
    (ginibreCoordinateDirection k) V hV (fun _ => Set.inter_subset_left) hcover
    _ θ hθ hc hs
  intro a η hη hcη hsη
  have he := ginibre_radial_rotated_weak_test n hn u g hg f hf hr a.val a.property
    (ginibreCoordinateDirection k) η hη hcη (hsη.trans Set.inter_subset_right)
  calc
    _ = ∫ z, (∑ j : Fin n × Fin 2,
        ginibreDirectionCoefficient (coordinatePhase a.val (ginibreCoordinateDirection k)) j *
          g (coordinatePhase a.val z) j) * η z := by
      apply integral_congr_ae
      filter_upwards [ginibre_radial_weak_gradient_phase_covariance n hn u g hg f hf hr
        a.val a.property] with z hz
      rw [hz k]
    _ = _ := he

end
end GinibrePoincare
