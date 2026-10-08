module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungInverse

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dolbeaultBoundedMultiplier_memLp {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) (u : dolbeaultOrdinaryL2 n) :
    MemLp (fun z => b z*u z) 2 volume := by
  apply ((Lp.memLp u).norm.const_mul C).mono' (hb.mul (Lp.aestronglyMeasurable u))
  filter_upwards [hC] with z hz
  change ‖b z*u z‖ ≤ _
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right hz (norm_nonneg _)

def dolbeaultBoundedMultiplierValue {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) (u : dolbeaultOrdinaryL2 n) :
    dolbeaultOrdinaryL2 n := (dolbeaultBoundedMultiplier_memLp b hb C hC u).toLp (fun z => b z*u z)

theorem dolbeaultBoundedMultiplier_ae {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) (u : dolbeaultOrdinaryL2 n) :
    (dolbeaultBoundedMultiplierValue b hb C hC u : Configuration n → ℂ) =ᵐ[volume]
      fun z => b z*u z := (dolbeaultBoundedMultiplier_memLp b hb C hC u).coeFn_toLp

theorem dolbeaultBoundedMultiplier_norm {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultBoundedMultiplierValue b hb C hC u‖ ≤ C*‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [dolbeaultBoundedMultiplier_ae b hb C hC u,hC] with z hz hc
  rw [hz,norm_mul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

def dolbeaultBoundedMultiplierLinear {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) :
    dolbeaultOrdinaryL2 n →ₗ[ℂ] dolbeaultOrdinaryL2 n where
  toFun := dolbeaultBoundedMultiplierValue b hb C hC
  map_add' u v := by
    apply Lp.ext
    filter_upwards [dolbeaultBoundedMultiplier_ae b hb C hC (u+v),
      dolbeaultBoundedMultiplier_ae b hb C hC u,dolbeaultBoundedMultiplier_ae b hb C hC v,
      Lp.coeFn_add u v,Lp.coeFn_add (dolbeaultBoundedMultiplierValue b hb C hC u)
        (dolbeaultBoundedMultiplierValue b hb C hC v)] with z h1 h2 h3 h4 h5
    simp only [Pi.add_apply] at h4 h5
    rw [h1,h5,h2,h3,h4]
    ring
  map_smul' c u := by
    apply Lp.ext
    filter_upwards [dolbeaultBoundedMultiplier_ae b hb C hC (c •u),
      dolbeaultBoundedMultiplier_ae b hb C hC u,Lp.coeFn_smul c u,
      Lp.coeFn_smul c (dolbeaultBoundedMultiplierValue b hb C hC u)] with z h1 h2 h3 h4
    simp only [RingHom.id_apply]
    simp only [Pi.smul_apply,smul_eq_mul] at h3 h4
    rw [h1,h4,h2,h3]
    ring

/-- Actual bounded multiplication, ready to compose with coordinate Cauchy–Green homotopies. -/
def dolbeaultBoundedMultiplier {n : ℕ} (b : Configuration n → ℂ)
    (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultBoundedMultiplierLinear b hb C hC).mkContinuous C (dolbeaultBoundedMultiplier_norm b hb C hC)

#print axioms dolbeaultBoundedMultiplier
#print axioms dolbeaultBoundedMultiplier_ae
end
end GinibrePoincare
