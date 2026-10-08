module

public import GinibrePoincare.Analysis.AlternativeBochnerKodairaInverseRoot
public import GinibrePoincare.Analysis.GinibreGeneratorDeficitAlgebra
public import GinibrePoincare.Endgame.FullTheoremOneTen

@[expose] public section

/-! # Independent integrated Bochner–Kodaira proof of Theorem 1.10

The second derivative energy is obtained from the Gaussian commutator and
integration by parts, extended through finite polynomial jet approximation.
Neither the first Hermite deficit nor Theorem 1.9 is invoked. The weak-domain
first identity and generator-domain second identity have their actual domains.
-/
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The first differential deficit, independently obtained from the integrated
Bochner–Kodaira identity, for every genuine real symmetric weak pair. -/
theorem bochnerKodaira_ginibre_weak_first_deficit {n : ℕ} (hn : 0 < n)
    (u : GinibreFullValueL2 n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u g)
    (hs : IsGinibreSymmetricWeakPair (u,g)) :
    ginibreWeakEnergy n g - 2*ginibreL2Variance n hn u =
      2*‖ginibreFullHolomorphicRemainder n hn u‖^2 +
        (4/(n:ℝ))*ginibreDifferentialSecondEnergy n hn g := by
  obtain ⟨huc,hsc⟩ := ginibreFullCenter_weak_pair hn u g hu hs
  have hc := ginibreFullTransformedDbar_weak_coefficient hn
    (ginibreFullCenter n hn u) g huc hsc
  have hBK := bkInverseSquareRoot_total_energy hn (ginibreFullCenteredTransform n hn u)
    (ginibreFullTransformedDbar n hn · g) hc
  have hw : ‖ginibreFullCenteredTransform n hn u‖^2 = ginibreL2Variance n hn u := by
    unfold ginibreFullCenteredTransform
    rw [(normalizedVandermondeL2 n hn).norm_map, ginibreFullCenteredValue_norm_sq]
  rw [ginibreFullTransformedDbar_norm_sum hn g, hw,
    ginibreFullWeak_zero_mode_norm hn u g hu hs] at hBK
  change ginibreDifferentialSecondEnergy n hn g = _ at hBK
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hE : (4/(n:ℝ))*ginibreDifferentialSecondEnergy n hn g =
      ginibreWeakEnergy n g - 4*ginibreL2Variance n hn u +
        4*‖ginibreFullHolomorphicPart n hn u‖^2 := by
    rw [hBK]
    unfold ginibreWeakEnergy
    field_simp
    ring
  have hgeom := ginibreFullWeak_holomorphic_geometry hn u g hu hs
  rw [hE]
  nlinarith

/-- Both exact differential identities, with ordinary Schwartz first and second
Wirtinger derivatives and the actual projected inverse square root, on the full
real symmetric generator graph. This is the independent Section 6 route. -/
theorem bochnerKodairaTheoremOneTen {n : ℕ} (hn : 0 < n)
    (u v : ginibreFullSymmetricValues n)
    (hgraph : (ginibreFullSymmetricOfReal n u, ginibreFullSymmetricOfReal n v) ∈
      (ginibreFullGenerator n hn).graph) :
    ∃ g : GinibreFullGradientL2 n,
      IsGinibreDistributionalGradient n u.val g ∧
      IsGinibreSymmetricWeakPair (u.val,g) ∧
      (∀ j, IsGaussianSchwartzDbar n (ginibreDifferentialDeficitVector n hn u.val)
        (ginibreDifferentialFirstDerivative n hn g j) j) ∧
      (∀ j k, IsGaussianSchwartzDbar n (ginibreDifferentialFirstDerivative n hn g j)
        (ginibreDifferentialSecondDerivative n hn g j k) k) ∧
      ginibreWeakEnergy n g - 2*ginibreL2Variance n hn u.val =
        2*‖ginibreFullHolomorphicRemainder n hn u.val‖^2 +
          (4/(n:ℝ))*ginibreDifferentialSecondEnergy n hn g ∧
      ‖v.val‖^2 - 2*ginibreWeakEnergy n g =
        ‖v.val + (2:ℝ) • ginibreFullCenter n hn u.val‖^2 +
          4*‖ginibreFullHolomorphicRemainder n hn u.val‖^2 +
          (8/(n:ℝ))*ginibreDifferentialSecondEnergy n hn g := by
  obtain ⟨g,hu,hs,hsecond⟩ := ginibreGenerator_second_deficit_algebra hn u v hgraph
  have hfirst := bochnerKodaira_ginibre_weak_first_deficit hn u.val g hu hs
  obtain ⟨hd,hdd⟩ := ginibreDifferentialDeficit_weak_derivatives hn u.val g hu hs
  refine ⟨g,hu,hs,fun j => (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr (hd j),
    fun j k => (gaussianSchwartzDbar_iff_weak hn _ _ k).mpr (hdd j k),hfirst,?_⟩
  rw [hsecond,hfirst]
  ring

#print axioms bochnerKodaira_ginibre_weak_first_deficit
#print axioms bochnerKodairaTheoremOneTen
end
end GinibrePoincare
