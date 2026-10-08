module

public import GinibrePoincare.Analysis.AlternativeBakryEmeryConvexLift
public import GinibrePoincare.Analysis.AlternativeBakryEmeryRadialLift
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-! # Identification of the literal block lift with its Hilbert potential
The configuration coordinates carry a sup norm, while the diffusion uses
the Euclidean norm. This file explicitly bridges those two representations.
-/

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The Euclidean block coordinates, with complex dimension `k+1`. -/
abbrev BakryEmeryHilbertBlock (k : ℕ) := EuclideanSpace ℂ (Fin (k + 1))

/-- The physical squared radius is the squared Hilbert norm, not the square
of the configuration's sup norm. -/
theorem bakryEmeryBlock_radius_eq_hilbert_norm_sq (k : ℕ) (x : Configuration (k + 1)) :
    gaussianBlockRadius 1 (k + 1) x =
      ‖(WithLp.toLp 2 x : BakryEmeryHilbertBlock k)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [gaussianBlockRadius, Nat.cast_one, one_mul, configurationNormSq,
    Complex.normSq_eq_norm_sq]

/-- The density in the literal Euclidean-volume construction uses precisely
the Hilbert potential whose strong convexity was proved. -/
theorem bakryEmeryBlock_profile_eq_hilbert_potential (n k : ℕ) (V : Potential)
    (x : Configuration (k + 1)) :
    (n : ℝ) * potentialSquaredRadiusProfile V (gaussianBlockRadius 1 (k + 1) x) =
      bakryEmeryEuclideanLiftPotential n V
        (WithLp.toLp 2 x : BakryEmeryHilbertBlock k) := by
  unfold potentialSquaredRadiusProfile bakryEmeryEuclideanLiftPotential
  rw [bakryEmeryBlock_radius_eq_hilbert_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The actual Hilbert block potential has exact `nρ` convexity, on the
Euclidean representation corresponding to the literal lift density. -/
theorem bakryEmeryBlock_hilbert_strongConvex (n k : ℕ) (ρ : ℝ) {V : Potential}
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ (Set.univ : Set (BakryEmeryHilbertBlock k))
      (fun x => bakryEmeryEuclideanLiftPotential n V x -
        ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) :=
  bakryEmeryEuclideanLift_strongConvex n ρ hrot hc

#print axioms bakryEmeryBlock_radius_eq_hilbert_norm_sq
#print axioms bakryEmeryBlock_profile_eq_hilbert_potential
#print axioms bakryEmeryBlock_hilbert_strongConvex

end
end GinibrePoincare
