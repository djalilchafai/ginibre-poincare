module

public import GinibrePoincare.Analysis.GinibreDrivenPathFactorization
public import GinibrePoincare.Analysis.GinibreBrownianProjection
public import GinibrePoincare.Analysis.GinibreDynamicsGenerator
public import GinibrePoincare.Analysis.GinibreStochasticCIRRealization
public import GinibrePoincare.Analysis.GinibreStochasticFullTwoRadiusRealization
public import GinibrePoincare.Analysis.BrownianOrthogonalIndependentInitial
public import GinibrePoincare.Analysis.GinibreHamiltonianStateTransitionKernel
public import GinibrePoincare.Analysis.GinibreHamiltonianEquilibriumProductLaw
public import GinibrePoincare.Analysis.GinibreStochasticStationaryTwoRadiusLaw
public import GinibrePoincare.Analysis.GinibreStochasticTransitionSemigroupIdentification

@[expose] public section

/-! # Reading route through stochastic dynamical factorization

This import facade collects the endpoints for the original singular
Brownian SDE. For a proof-oriented reading order:

1. `GinibreDrivenPathFactorization`: project the deterministic Volterra
   equation to the center OU equation and the relative equation.
2. `GinibreBrownianProjection`: prove orthogonality and independence of
   the projected Brownian noises.
3. `GinibreStochasticNoncollision` (imported transitively): construct the
   Hamiltonian martingales and conclude infinite lifetime and noncollision.
4. `BrownianOrthogonalIndependentInitial`: transfer independent input
   pairs through the measurable solution maps to independent entire paths.
5. `GinibreStochasticFullTwoRadiusRealization`: construct independent
   scalar drivers and both localized CIR equations, including zero speed
   and zero initial center.
6. `GinibreHamiltonianStateTransitionKernel`: assemble the genuine
   transition kernels and their Markov properties.
7. `GinibreHamiltonianEquilibriumProductLaw` and
   `GinibreStochasticStationaryTwoRadiusLaw`: obtain invariance of the
   original process and the independent Gamma law of the two radii at each time.
8. `GinibreStochasticTransitionSemigroupIdentification`: identify the
   original stochastic evolution with the analytic paper-speed evolution
   on the full symmetric L² space.

The deterministic and stochastic endpoints keep their individual domains:
noncollision and path factorization need a positive particle count; the
relative-radius CIR endpoints require at least two particles. Speed is
nonnegative in the global original-process assertions. Integral identities
are localized by bounded Hamiltonian stops, with exhaustion established in
`GinibreStochasticLocalizationExhaustion`. -/
