module

public import GinibrePoincare.Analysis.GinibreFullSemigroupConservation
public import GinibrePoincare.Analysis.GinibreFullSemigroupDifferentiability

@[expose] public section

/-! # Actual full generator-domain diffusion evolution -/
open MeasureTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Full generator-domain observables evolve differentiably at every positive time. -/
theorem ginibreFullEvolution_hasDerivAt (n : ℕ) (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hp : (u, v) ∈ (ginibreFullGenerator n hn).graph)
    {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s : ℝ => ginibreFullEvolution n hn (Real.toNNReal s) u)
      (ginibreFullEvolution n hn (Real.toNNReal t) v) t :=
  resolventGenerator_orbit_hasDerivAt _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_spectrum n hn)
    (ginibreFullComplexResolvent_denseRange n hn) u v hp ht

/-- The full diffusion equation in integrated Hilbert-space form. -/
theorem ginibreFullEvolution_integral_equation (n : ℕ) (hn : 0 < n)
    (u v : ginibreSymmetricL2 n) (hp : (u, v) ∈ (ginibreFullGenerator n hn).graph)
    {t : ℝ} (ht : 0 ≤ t) :
    ginibreFullEvolution n hn (Real.toNNReal t) u = u +
      ∫ s in (0 : ℝ)..t, ginibreFullEvolution n hn (Real.toNNReal s) v :=
  resolventGenerator_orbit_integral _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) (ginibreFullComplexResolvent_spectrum n hn)
    (ginibreFullComplexResolvent_denseRange n hn) u v hp ht

/-- Exact exponential action on every genuine full-generator eigenfunction. -/
theorem ginibreFullEvolution_eigenvector (n : ℕ) (hn : 0 < n) (t : ℝ≥0)
    (rate : ℝ) (hRate : 0 ≤ rate) (u : ginibreSymmetricL2 n)
    (hu : (u, -(rate : ℂ) • u) ∈ (ginibreFullGenerator n hn).graph) :
    ginibreFullEvolution n hn t u = Real.exp (-rate * (t : ℝ)) • u :=
  resolventCfcEvolution_generator_eigenvector _ (ginibreFullComplexResolvent_isSelfAdjoint n hn)
    (ginibreFullComplexResolvent_injective n hn) t rate hRate u hu

end
end GinibrePoincare
