module

public import GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathElement
public import GinibrePoincare.Analysis.GinibreCollisionCutoffEnergy

@[expose] public section

open Set MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A collision-free version of an initial configuration, changing only collisions. -/
def ginibreFreeInitialVersion {n : ℕ} (z₀ : Configuration n) (hz₀ : CollisionFree z₀)
    (z : Configuration n) : {z : Configuration n // CollisionFree z} := by
  classical
  exact if h : CollisionFree z then ⟨z, h⟩ else ⟨z₀, hz₀⟩

theorem ginibreFreeInitialVersion_measurable {n : ℕ}
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀) :
    Measurable (ginibreFreeInitialVersion z₀ hz₀) := by
  classical
  apply Measurable.subtype_mk
  have hm : Measurable (fun z : Configuration n => if CollisionFree z then z else z₀) :=
    measurable_id.ite (isOpen_collisionFree n).measurableSet
    (measurable_const (a := z₀))
  convert hm using 1
  funext z
  change (if h : CollisionFree z then (⟨z, h⟩ : {z : Configuration n // CollisionFree z})
    else ⟨z₀, hz₀⟩).val = (if CollisionFree z then z else z₀)
  by_cases hz : CollisionFree z
  · rw [dif_pos hz, if_pos hz]
  · rw [dif_neg hz, if_neg hz]

theorem ginibreFreeInitialVersion_ae_eq {n : ℕ} (hn : 0 < n)
    (z₀ : Configuration n) (hz₀ : CollisionFree z₀) :
    (fun z => (ginibreFreeInitialVersion z₀ hz₀ z).val) =ᵐ[ginibreMeasure n] id := by
  classical
  filter_upwards [ginibre_ae_collisionFree n hn] with z hz
  simp [ginibreFreeInitialVersion, hz]

end
end GinibrePoincare
