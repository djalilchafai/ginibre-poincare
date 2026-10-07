module

public import GinibrePoincare.Analysis.GinibreGradientPhaseNorm
public import GinibrePoincare.Analysis.GinibrePhaseSeparation
public import GinibrePoincare.Analysis.GinibreLocalSobolev

@[expose] public section

/-! # Radial weak L² regularity through collisions away from coordinate zeroes -/

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Phase invariant local integrability extends across collisions whenever all
coordinates are nonzero. -/
theorem phase_invariant_locallyIntegrable_nonzero (n : ℕ) (hn : 0 < n)
    (F : Configuration n → ℝ)
    (hF : LocallyIntegrableOn F {z | CollisionFree z} volume)
    (hp : ∀ a : Fin n → ℂ, ∀ _ha : ∀ i, ‖a i‖ = 1,
      ∀ᵐ z ∂(volume : Measure (Configuration n)), F (coordinatePhase a z) = F z) :
    LocallyIntegrableOn F {z | ∀ i, z i ≠ 0} volume := by
  intro z hz
  obtain ⟨a, ha, hs⟩ := exists_coordinatePhase_collisionFree n hn z hz
  let e := coordinatePhaseCLE n a ha
  have hc := locallyIntegrableOn_comp_volume_equiv n e
    (measurePreserving_coordinatePhaseCLE_volume n a ha)
    {z | CollisionFree z} (isOpen_collisionFree n) F hF
  have he : (F ∘ e) =ᵐ[volume] F := hp a ha
  have hl : LocallyIntegrableOn F (e ⁻¹' {z | CollisionFree z}) volume :=
    hc.congr (ae_restrict_of_ae he)
  have hm : z ∈ e ⁻¹' {z | CollisionFree z} := hs
  have hi := hl z hm
  rw [nhdsWithin_eq_nhds.mpr ((isOpen_collisionFree n).preimage e.continuous |>.mem_nhds hm)] at hi
  exact hi.filter_mono nhdsWithin_le_nhds

/-- Radial weighted L² values are locally ordinary L² through collisions away
from the coordinate zero sets. -/
theorem ginibre_radial_value_norm_sq_locallyIntegrable_nonzero (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    LocallyIntegrableOn (fun z => ‖u z‖ ^ 2) {z | ∀ i, z i ≠ 0} volume := by
  apply phase_invariant_locallyIntegrable_nonzero n hn _
    (ginibre_memLp_norm_sq_locallyIntegrable_collisionFree hn u (Lp.memLp u))
  intro a ha
  filter_upwards [ginibre_radial_L2_phase_ae n hn u f hf hr a ha] with z hz
  rw [hz]

/-- The actual weak gradient of a radial value has the same local ordinary L²
regularity, including collision configurations with nonzero coordinates. -/
theorem ginibre_radial_gradient_norm_sq_locallyIntegrable_nonzero (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i))) :
    LocallyIntegrableOn (fun z => ‖g z‖ ^ 2) {z | ∀ i, z i ≠ 0} volume := by
  apply phase_invariant_locallyIntegrable_nonzero n hn _
    (ginibre_memLp_norm_sq_locallyIntegrable_collisionFree hn g (Lp.memLp g))
  intro a ha
  filter_upwards [ginibre_radial_weak_gradient_norm_phase_ae n hn u g hg f hf hr a ha] with z hz
  rw [hz]

/-- A radial weak value belongs to ordinary L² on every compact set disjoint
from coordinate zeroes; collisions inside the compact set are allowed. -/
theorem ginibre_radial_value_memLp_compact_nonzero (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n)) (f : Configuration n → ℝ)
    (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | ∀ i, z i ≠ 0}) :
    MemLp (u : Configuration n → ℝ) 2 (volume.restrict K) := by
  have hm : AEStronglyMeasurable (u : Configuration n → ℝ) volume :=
    AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable u)
  apply (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
  exact (ginibre_radial_value_norm_sq_locallyIntegrable_nonzero n hn u f hf hr).integrableOn_compact_subset hs hK

/-- The actual radial weak gradient belongs to ordinary L² on those compact
sets as well, without a separate unweighted integrability assumption. -/
theorem ginibre_radial_gradient_memLp_compact_nonzero (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (f : Configuration n → ℝ) (hf : (u : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f)
    (hr : ∃ F : (Fin n → ℝ) → ℝ, ∀ z, f z = F (fun i => Complex.normSq (z i)))
    (K : Set (Configuration n)) (hK : IsCompact K) (hs : K ⊆ {z | ∀ i, z i ≠ 0}) :
    MemLp (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) 2 (volume.restrict K) := by
  have hm : AEStronglyMeasurable
      (g : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) volume :=
    AEStronglyMeasurable.mono_ac (volume_absolutelyContinuous_ginibreMeasure n hn)
      (Lp.aestronglyMeasurable g)
  apply (memLp_two_iff_integrable_sq_norm hm.restrict).mpr
  exact (ginibre_radial_gradient_norm_sq_locallyIntegrable_nonzero n hn u g hg f hf hr).integrableOn_compact_subset hs hK

end
end GinibrePoincare
