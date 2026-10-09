module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticWeakCore

@[expose] public section

namespace GinibrePoincare
noncomputable section

/-- The genuine unique distributional gradient inherits symmetry from the
actual symmetric L² value. No gradient symmetry assumption is needed. -/
theorem ginibreFullSymmetricValue_distributional_pair_symmetric {n : ℕ} (hn : 0 < n)
    (u : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g) :
    IsGinibreSymmetricWeakPair (u.val, g) := by
  intro σ
  refine ⟨u.property σ,?_⟩
  have hp := ginibreDistributionalGradient_permute hn σ u.val g hu
  rw [u.property σ] at hp
  exact ginibre_distributional_gradient_unique n hn u.val _ g hp hu

/-- A genuine full distributional resolvent with the literal compact-core
equation is the analytic resolvent; its weak-pair symmetry is derived. -/
theorem ginibreTransitionAnalytic_resolvent_from_core_distributional {n : ℕ} (hn : 0 < n)
    (f u : ginibreFullSymmetricValues n) (g : GinibreFullGradientL2 n)
    (hu : IsGinibreDistributionalGradient n u.val g)
    (heq : ∀ (φ : Configuration n → ℝ) (hφ : IsTheoremOneNineCore φ),
      inner ℝ u.val (ginibreFullCoreValue hn φ hφ)+
        (1/(n : ℝ))*inner ℝ g (ginibreFullCoreGradient hn φ hφ)=
          inner ℝ f.val (ginibreFullCoreValue hn φ hφ)) :
    ginibreFullSymmetricResolvent n hn f=u :=
  ginibreTransitionAnalyticWeakCore_resolvent hn f u g hu
    (ginibreFullSymmetricValue_distributional_pair_symmetric hn u g hu) heq

#print axioms ginibreFullSymmetricValue_distributional_pair_symmetric
#print axioms ginibreTransitionAnalytic_resolvent_from_core_distributional
end
end GinibrePoincare
