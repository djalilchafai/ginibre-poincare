module

public import GinibrePoincare.Analysis.GeneralPotentialSharpPoincare
public import GinibrePoincare.Analysis.StrongConvexPotentialRadialLipschitzLSI

@[expose] public section

/-! # Both concrete functional inequalities for nonquadratic potentials -/
namespace GinibrePoincare
noncomputable section

theorem fullNonQuadraticPotentialTheorem (n : ℕ) (hn : 0 < n) :
    NonQuadraticPotentialTheorem n := by
  constructor
  · intro V ρ hV hrot hfin hρ hsub f hf
    exact rhoSubharmonic_potential_smooth_poincare hn hV hrot hfin ρ hρ hsub f hf
  · intro V ρ hV hrot hfin hρ hconv f hf hr
    simpa only [mul_comm (n : ℝ) ρ] using
      rhoConvex_potential_smooth_radial_lsi n hn ρ hρ hV hrot hconv f hf hr

#print axioms fullNonQuadraticPotentialTheorem
end
end GinibrePoincare
