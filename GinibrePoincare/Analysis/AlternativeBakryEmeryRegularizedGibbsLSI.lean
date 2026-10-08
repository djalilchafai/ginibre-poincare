module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryConvexGibbsLSI
public import GinibrePoincare.Analysis.AlternativeBakryEmeryRegularizedEuclidean
@[expose] public section
open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- Concrete Bakry–Émery inequality for the actual smooth radial Euclidean
lift, with the exact paper curvature `nρ` and no analytic completion inputs. -/
theorem bakryEmeryRegularizedLiftGibbs_square_lsi
    (n d : ℕ) (hn : 0 < n) (hd : 0 < d) (ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (V : Potential) (hV : ContDiff ℝ 2 V)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V)
    (f : EuclideanSpace ℝ (Fin d×Fin 2) → ℝ)
    (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume
      (bakryEmeryRegularizedLiftPotential (E := EuclideanSpace ℝ (Fin d×Fin 2)) n V ε)) f ≤
      (2/((n:ℝ)*ρ))*∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
        (bakryEmeryRegularizedLiftPotential (E := EuclideanSpace ℝ (Fin d×Fin 2)) n V ε) := by
  have hκ : 0 < (n:ℝ)*ρ := mul_pos (by exact_mod_cast hn) hρ
  have hh := bakryEmeryConfigurationGibbs_square_lsi d hd
    (bakryEmeryRegularizedConfigurationPotential n d V ε)
    (bakryEmeryRegularizedConfigurationPotential_contDiff n d V ε hV hε)
    ((n:ℝ)*ρ) hκ
    (bakryEmeryRegularizedConfigurationPotential_euclidean_strongConvex n d ρ ε V hrot hc)
    f hf hs
  rw [bakryEmeryRegularizedConfigurationPotential_euclidean] at hh
  exact hh

#print axioms bakryEmeryRegularizedLiftGibbs_square_lsi
end
end GinibrePoincare
