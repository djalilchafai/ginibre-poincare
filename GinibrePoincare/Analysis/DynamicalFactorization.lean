module

public import GinibrePoincare.Analysis.GinibreDrivenPathFactorization
public import GinibrePoincare.Analysis.GinibreBrownianProjection
public import GinibrePoincare.Analysis.GinibreDynamicsGenerator
public import GinibrePoincare.Analysis.GinibreStochasticFullTwoRadiusRealization
public import GinibrePoincare.Analysis.BrownianOrthogonalIndependentInitial
public import GinibrePoincare.Analysis.GinibreHamiltonianStateTransitionKernel
public import GinibrePoincare.Analysis.GinibreHamiltonianEquilibriumProductLaw
public import GinibrePoincare.Analysis.GinibreStochasticStationaryTwoRadiusLaw
public import GinibrePoincare.Analysis.GinibreStochasticTransitionSemigroupIdentification

@[expose] public section

/-! # Actual stochastic dynamical factorization

The canonical original singular Brownian SDE is globally collision-free almost
surely. Its center and relative paths are independent for deterministic initial
states and for probability initial laws with independent center and relative
projections. Actual original-noise integrals give independent center and relative
Brownian drivers and both literal localized CIR equations with exhausting stops,
for every nonnegative speed and every collision-free initial configuration,
including zero initial center. The genuine transition kernels have the
Chapman–Kolmogorov and tested-past Markov identities.

The literal original process preserves the exact Ginibre measure. Its genuine
equilibrium path law reverses on every horizon, and the two CIR observables have
the independent Gamma product law at every time. The literal original stochastic transitions equal the analytic paper-speed
semigroup on every symmetric L² input, for every nonnegative speed and horizon. No completion
instance or vacuous certificate is introduced here.
-/
