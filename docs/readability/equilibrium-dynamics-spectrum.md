# Equilibrium, dynamics and spectrum

[Reading index](../../HUMAN_READABILITY.md) · [Verified revision and current evidence](../../STATUS.md)

## Theorem 1.2: equilibrium coordinates

[EquilibriumFactorization](../../GinibrePoincare/Analysis/EquilibriumFactorization.lean)
introduces the linear splitting into the coordinate sum and the zero-sum
configuration. Distinguish the sum from the average: the probability endpoint
uses the sum, whose law is the standard complex Gaussian in this normalization.

[EquilibriumProbability](../../GinibrePoincare/Analysis/EquilibriumProbability.lean)
then proceeds from geometry to probability. `equilibriumCoordinates_map_volume`
obtains a positive constant Jacobian by Haar uniqueness. The pointwise density
factorization yields a product measure. The recentered marginal is defined as
the pushforward of the actual Ginibre measure; its normalization therefore
follows from the existing probability normalization. Read `equilibrium_jointLaw`,
`coordinateSum_ginibre_gaussian`, and `coordinateSum_recentered_indepFun` as the
three interfaces: product law, Gaussian marginal, independence.

The Gamma radius law is a further result in
[GinibreRadialGamma](../../GinibrePoincare/Analysis/GinibreRadialGamma.lean).
The probability factorization module deliberately does not prove it. Its proof
route uses homogeneous weighted-measure scaling, as explained in
[REPORT.md](../../REPORT.md#theorem-12-homogeneous-measure-scaling-for-the-gamma-radius).

## Theorem 1.3: dynamics and localization

Use [DynamicalFactorization](../../GinibrePoincare/Analysis/DynamicalFactorization.lean)
as the topic facade, then follow three separate questions.

1. **Which process is being solved?**
   [GinibreDrivenPathFactorization](../../GinibrePoincare/Analysis/GinibreDrivenPathFactorization.lean)
   treats the original driven equation under the center/relative coordinate
   change. [GinibreBrownianProjection](../../GinibrePoincare/Analysis/GinibreBrownianProjection.lean)
   handles projected Brownian noise. Independence of random initial projections
   is an additional hypothesis for independence of the two resulting processes.
2. **Where do radial Brownian drivers and CIR equations come from?**
   [GinibreStochasticFullTwoRadiusRealization](../../GinibrePoincare/Analysis/GinibreStochasticFullTwoRadiusRealization.lean)
   packages the two drivers and localized radius equations. Read its statement
   in groups: Brownian law; driver independence; filtration/measurability;
   stopping times and exhaustion; path continuity; stochastic left-sum limits;
   the two equations. The joint realization assumes `n ≥ 2` and a collision-free
   deterministic initial configuration. Zero initial center is allowed.
3. **How are stops removed?**
   [CorrespondenceDynamicsGlobalCIR](../../GinibrePoincare/Analysis/CorrespondenceDynamicsGlobalCIR.lean)
   first proves `correspondence_global_CIR_integral_of_local`, a reusable lemma
   whose local inputs are explicit hypotheses. The concrete endpoint
   `correspondence_ginibre_global_independent_CIR_equations` supplies those
   inputs from the realization. `correspondenceCIRIntegral` is expressed using
   the radius and its drift; convergence of Brownian left sums is what justifies
   interpreting this expression as the stochastic integral.

For the relative-radius equation, the named endpoint in
[GinibreStochasticCIRRealization](../../GinibrePoincare/Analysis/GinibreStochasticCIRRealization.lean)
separates the scalar driver, stopping-time exhaustion, radius path properties
and each stopped integral. With its hypotheses in scope:

```lean
obtain ⟨β, driver, localization, radiusPaths, integrals⟩ :=
  ginibreBrownianMaximalProcess_CIR_realization_named hn α z hz B P hB hind
have hBrownian := driver.brownian
have hExhaustion := localization.exhausts
obtain ⟨J, integral⟩ := integrals R hR T
have hMeanSquare := integral.meanSquareLimit
have hEquation := integral.equation
```

`CIRScalarDriver` also names martingale, square-integrability and fresh-increment
properties. `CIRExhaustingLocalization` names stopping-time, monotonicity and
pathwise exhaustion facts. `CIRStoppedIntegral` names the two sum-limit clauses,
continuity, initial value and the equation. The integral's limit clauses cover
`t ≤ T`; the equation covers `t ≤ σ ω`. Continuity of `J` is stated for every
sample, whereas the equation holds on one full-measure event. The named result
is the relative-radius interface; the joint independent-driver theorem remains
a separate result.

Stationarity and transition identification are subsequent interfaces, not
consequences of the CIR tuple alone. Read
[GinibreEquilibriumProcessStationarityPath](../../GinibrePoincare/Analysis/GinibreEquilibriumProcessStationarityPath.lean)
for whole-path equilibrium stationarity and
[GinibreStochasticTransitionResolventIdentification](../../GinibrePoincare/Analysis/GinibreStochasticTransitionResolventIdentification.lean)
for the normalized Laplace integral. The public
[FullPaper](../../GinibrePoincare/Endgame/FullPaper.lean) lists the unrestricted
martingale problem, strong Markov and semigroup endpoints alongside their exact
names, providing starting points for deeper navigation.

## Theorem 1.4 and Corollary 1.5: polynomials and spectrum

Start at [PolynomialEigenfunctions](../../GinibrePoincare/Analysis/PolynomialEigenfunctions.lean)
for the Hermite–Laguerre family and indices. Its observables depend on the
coordinate sum and recentered radius. Then read
[PolynomialEigenfunctionGenerator](../../GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean):
`polynomialEigenfunction_eigenvalue_equation_atSpeed` proves the pointwise
collision-free pregenerator equation. This module explicitly distinguishes
that equation from closed-generator domain membership.

[PolynomialEigenfunctionBasis](../../GinibrePoincare/Analysis/PolynomialEigenfunctionBasis.lean)
provides finite expansions and equilibrium orthogonality.
[PolynomialGeneratorSpectrum](../../GinibrePoincare/Analysis/PolynomialGeneratorSpectrum.lean)
connects the sector to the closed generator.
[PolynomialSectorIncompleteness](../../GinibrePoincare/Analysis/PolynomialSectorIncompleteness.lean)
explains why that sector is proper; a basis for this sector is not a basis for
all symmetric L² observables.

For Corollary 1.5, the shorter route is
[GinibreOneParticleSpectrum](../../GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean).
It constructs coordinate-sum powers, proves their gradients square-integrable,
places them in the actual generator graph, and proves squared norms `k!`.
Thus the eigenvectors are nonzero. The final theorem
`ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment` applies to
all `n > 0`, including one particle, and positive speed. Its spectrum means
absence of a bounded two-sided inverse on the unbounded operator's exact graph
domain. This differs from applying the algebraic spectrum of a bounded operator.
The Hermite–Laguerre relative-radius construction uses `n ≥ 2`.
