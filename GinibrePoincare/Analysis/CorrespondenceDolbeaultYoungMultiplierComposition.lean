module
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMultiplier

@[expose] public section
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The derivative-free residual operator in coordinate Dolbeault homotopy. -/
def dolbeaultResidualOperator {n : ℕ} (j : Fin n) (R : ℝ)
    (b : Configuration n → ℂ) (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultCauchyGreenL2 j R).comp (dolbeaultBoundedMultiplier b hb C hC)

theorem dolbeaultResidualOperator_norm {n : ℕ} (j : Fin n) (R : ℝ)
    (b : Configuration n → ℂ) (hb : AEStronglyMeasurable b volume) (C : ℝ)
    (hC : ∀ᵐ z : Configuration n ∂volume, ‖b z‖≤C) (u : dolbeaultOrdinaryL2 n) :
    ‖dolbeaultResidualOperator j R b hb C hC u‖ ≤
      ((∫ y : ℂ, ‖dolbeaultTruncatedCauchyGreen R y‖)*C)*‖u‖ := by
  apply (dolbeaultCauchyGreenL2_norm j R (dolbeaultBoundedMultiplier b hb C hC u)).trans
  have h := mul_le_mul_of_nonneg_left (dolbeaultBoundedMultiplier_norm b hb C hC u)
    (integral_nonneg (μ := volume) (fun y => norm_nonneg (dolbeaultTruncatedCauchyGreen R y)))
  change (∫ y : ℂ, ‖dolbeaultTruncatedCauchyGreen R y‖)*
    ‖dolbeaultBoundedMultiplierValue b hb C hC u‖ ≤ _
  simpa only [mul_assoc] using h

/-- A finite sequence of genuine bounded homotopy/residual maps. -/
def dolbeaultFiniteOperators {n : ℕ}
    (Ts : List (dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n)) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  Ts.foldr (fun T S => T.comp S) (ContinuousLinearMap.id ℂ _)

/-- Ordinary strong L² approximation passes through every finite coordinate iteration. -/
theorem dolbeaultFiniteOperators_tendsto {n : ℕ} {ι : Type*} {l : Filter ι}
    (Ts : List (dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n))
    (u : ι → dolbeaultOrdinaryL2 n) (v : dolbeaultOrdinaryL2 n)
    (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun i => dolbeaultFiniteOperators Ts (u i)) l
      (𝓝 (dolbeaultFiniteOperators Ts v)) :=
  (dolbeaultFiniteOperators Ts).continuous.continuousAt.tendsto.comp hu

#print axioms dolbeaultResidualOperator_norm
#print axioms dolbeaultFiniteOperators_tendsto
end
end GinibrePoincare
