module

public import GinibrePoincare.Endgame.FullMainAnalyticProof
public import GinibrePoincare.Analysis.GinibreEntireProjectionEndpoints
public import GinibrePoincare.Analysis.GaussianCanonicalDbarSolution
public import GinibrePoincare.Analysis.GaussianEntireDistance
public import GinibrePoincare.Analysis.GaussianGinibreProjectionIntertwining
public import GinibrePoincare.Analysis.GinibreEntireProjectionGeometry
public import GinibrePoincare.Analysis.GinibreEntireProjectionDistance
public import GinibrePoincare.Analysis.EntireVandermondeFactorization
public import GinibrePoincare.Analysis.GaussianEntireSpaceClosure
public import GinibrePoincare.Analysis.GaussianDbarEqualitySpace
public import GinibrePoincare.Analysis.GinibreCenterProjectionClasses
public import GinibrePoincare.Analysis.GinibreCenterProjectionGaussian
public import GinibrePoincare.Analysis.GinibreEntireProjectionBridge
public import GinibrePoincare.Analysis.GaussianEntireReconstruction
public import GinibrePoincare.Analysis.GinibreCenterProjectionEquality
public import GinibrePoincare.Analysis.GaussianDbarCompactCore
public import GinibrePoincare.Analysis.GaussianEntireHilbertIdentification
public import GinibrePoincare.Analysis.GaussianClosedFormVolume
public import GinibrePoincare.Analysis.GaussianDbarWeakEquality
public import GinibrePoincare.Analysis.GinibreComplexProjectionGeometry
public import GinibrePoincare.Analysis.GaussianFirstModeCreation
public import GinibrePoincare.Analysis.HermiteRodriguesHolomorphicLowering
public import GinibrePoincare.Analysis.GinibreRadiusNotHolomorphic
public import GinibrePoincare.Endgame.FullTheoremOneNine
public import GinibrePoincare.Endgame.FullTheoremOneTen
public import GinibrePoincare.Endgame.FullMatrixLift
public import GinibrePoincare.Endgame.FullNonQuadraticPotential
public import GinibrePoincare.Analysis.DynamicalFactorization
public import GinibrePoincare.Analysis.GinibreStochasticTransitionResolventIdentification
public import GinibrePoincare.Analysis.GinibreCollisionCapacity
public import GinibrePoincare.Analysis.GinibrePointwiseCurvature
public import GinibrePoincare.Analysis.GinibrePointwiseCurvatureTangent
public import GinibrePoincare.Analysis.PolynomialSectorIncompleteness
public import GinibrePoincare.Analysis.GinibreNonsymmetricCounterexample
public import GinibrePoincare.Analysis.GinibreLinearStatisticPoincare
public import GinibrePoincare.Analysis.HermiteRodriguesMultivariate
public import GinibrePoincare.Analysis.GinibreGeneratorGradientCommutation
public import GinibrePoincare.Analysis.GinibrePointwiseBochner
public import GinibrePoincare.Analysis.GinibreEquilibriumProcessStationarityPath
public import GinibrePoincare.Analysis.PolynomialGeneratorSpectrum
public import GinibrePoincare.Analysis.GinibreOneParticleSpectrum
public import GinibrePoincare.Analysis.GinibreGraphNormEquivalence
public import GinibrePoincare.Analysis.HermiteSecondDbarCombinatorics
public import GinibrePoincare.Analysis.HermiteSecondDbarEnergy
public import GinibrePoincare.Analysis.GinibreRealCoreClosureEquivalence
public import GinibrePoincare.Analysis.GinibreComplexCoreClosureEquivalence
public import GinibrePoincare.Analysis.GaussianDbarDistributionalClosure

@[expose] public section

/-! # Public full-paper entry point

The concrete paper results are exported on their stated domains:

* `fullTheoremOneNine`: both exact deficits on the full real generator graph,
  with sharp equality classification on the entire symmetric weak domain.
* `fullTheoremOneTen`: both differential deficits, with the actual projected
  inverse square root and genuine weak second Wirtinger derivatives. Their
  energy is the literal Gaussian integral of the squared derivatives.
* `fullMatrixLift_functional_inequalities`: variance and entropy bounds under
  the actual Gaussian matrix law and its genuine finite overlap energy.
* `fullNonQuadraticPotentialTheorem`: sharp symmetric Poincaré under the
  actual Laplacian bound, and radial log-Sobolev under actual strong convexity.
* `ginibreBrownian_full_two_radius_independent_CIR_realization`: the original
  singular Brownian process, two independent drivers and both localized CIR
  equations with genuine exhausting stops.
* `ginibreBrownian_equilibrium_original_invariant`: exact Ginibre marginals
  of the literal equilibrium-initialized original Brownian process.
* `ginibreOriginalStochasticL2Resolvent_eq_analytic`: identification of the
  literal stochastic normalized Laplace integral and the analytic unit resolvent.
* `ginibreOriginalSymmetricStochasticL2Operator_eq_paper`: the actual original
  Brownian transition semigroup equals the analytic paper evolution for every
  nonnegative speed, time and symmetric L² input.
* `polynomialSector_incomplete`: the actual closed polynomial sector is proper,
  witnessed by the nonzero centered quadratic and genuine relative-phase invariance.
* `ginibre_nonsymmetric_poincare_constant_lower_bound`: the actual coordinate
  counterexample gives the nonsymmetric lower bound (n+1)/4 for n≥2.
* `ginibreLinearStatistic_poincare`: sharp dimension-free transfer to the actual
  C¹ Lipschitz linear-statistic pushforward law.
* `ComplexHermite.multivariateNormalized_rodrigues`: the literal sequential
  Wirtinger derivatives of the actual Gaussian, with exact factorial constants.
* `ginibrePregenerator_gradient_commutation`: the actual differential operator
  commutes with directional differentiation up to the genuine Hamiltonian Hessian.
* `ginibrePointwiseGammaTwo_bochner`: the actual pointwise Bochner formula;
  `ginibrePointwiseGammaTwo_eq_iterated` identifies the literal iterated carré du champ.
* `ginibreEquilibriumPositivePath_shift_law`: true whole-path equilibrium
  stationarity, also exported as literal original-process finite-dimensional laws.
* `ginibreCollisionSet_capacity_zero`: zero capacity for the literal weighted
  ordinary weak-H¹ capacity infimum.
* `ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment`: Corollary 1.5
  for every n > 0, using the bounded two-sided resolvent spectrum of the actual
  unbounded full generator at arbitrary positive speed.
* `ginibre_gradient_graph_norm_equivalence`: the positive-speed norm comparison
  in Lemma A.2, on actual weighted L² value/gradient pairs.
* `ginibreComplexSmoothCore_closure_equivalence`: the equality of the global
  and collision-free compact smooth complex gradient graph closures in Lemma A.2.

The finite and infinite second-Wirtinger energy formulas are exported along
with their independently defined compact-test weak derivative graphs.
* `ginibre_pointwise_bakry_emery_curvature_unbounded_below` and
  `ginibre_pointwise_mean_curvature`: genuine Hamiltonian Hessian conclusions.

These exports use the actual measures, domains, processes and operators. Their
analytic constructions and regularity conclusions are proved in the imported
modules rather than supplied as completion assumptions.
-/
