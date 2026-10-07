# Ginibre Poincaré formalization report

Updated on 2026-10-07 after the final full-project build and both axiom audits.

Paper: Djalil Chafaï, *An optimal Poincaré inequality for the complex Ginibre log-gas*.

arXiv URL (authoritative version): <https://arxiv.org/abs/2608.19358v2>

The asserted numbered results of [arXiv:2608.19358v2](https://arxiv.org/abs/2608.19358v2) now have compiled concrete endpoints, including both Theorem 1.9 identities, Theorem 1.10 with ordinary distributional derivatives, the full weak-domain equality classification, stochastic dynamics, matrix overlaps and nonquadratic extensions. The remaining Gaussian/entire-function obligations are closed: maximal Schwartz domain, canonical minimal dbar solver, global entire Vandermonde division, actual entire-space projection geometry and literal representative distances. The original main analytic proof is also assembled without analytic completion hypotheses in [FullMainAnalyticProof](GinibrePoincare/Endgame/FullMainAnalyticProof.lean). Open research problems and numerical experiments are distinguished below. See [STATUS.md](STATUS.md) for the dashboard and [FullPaper.lean](GinibrePoincare/Endgame/FullPaper.lean) for public endpoints.

## Palomar verification checkpoint

Lean and the existing Mathlib checkout are upgraded together to v4.35.0-rc2. The final single-thread full build, source audit, 5,079 public axiom queries, 11,112-declaration all-local audit and both root compatibility checks pass. Actual Comparator passes strict recursive statement comparison and all three kernels: con-ron, nanoda and Lean’s default kernel. The independent Challenge has exactly the user-authorized statement hole; the proof library and Solution remain hole-free and use only the three permitted standard axioms. The comparison covers full symmetric weak-H¹ Theorem 1.1 and exhaustive affine equality, not the whole paper. Offline preflight reports zero blockers and metadata passes the official v0.4 schema. No registry submission has occurred.

## Subproject organization

The development is grouped into twelve buildable thematic import entry points: complex Gaussian/Hermite, Gaussian LSI/entropy, Ginibre measure/holomorphic geometry, weak Sobolev/collision capacity, deficits/equality, polynomial/radial/equilibrium sectors, generators/semigroups, stochastic calculus, stochastic dynamics, matrix lifts, nonquadratic potentials and final assembly. [SUBPROJECTS.md](SUBPROJECTS.md) gives every library file its unique primary group, direct dependency groups and physical line counts. [subprojects.json](subprojects.json) is the machine-readable manifest. Run `python3 scripts/group_subprojects.py --check` to verify the generated inventory; run `lake build GinibrePoincare.Subprojects.ComplexGaussianHermite` (or another facade name) to build a group. The root entry point now imports these twelve facades instead of a flat module list. `make audit` checks inventory freshness. Existing source paths and theorem names are retained.

## Full-project dashboard

| Workstream / paper statements | Verified scope |
| --- | --- |
| Complex Gaussian, Hermite analysis and Gaussian LSI | Concrete measures, complete tensor basis, Parseval, lowering, sharp Gaussian LSI |
| Ginibre measure and Vandermonde transform | Normalization, weighted L² isometry, global entire division and exact representative distances |
| Theorem 1.1 | Full symmetric weak-H¹ sharp Poincaré inequality and exhaustive equality classification; original analytic proof assembled |
| Theorem 1.2 | Equilibrium factorization, Gaussian center and recentered Gamma law |
| Theorem 1.3 | Original Brownian SDE, stochastic factorization, CIR realizations, invariance, stationarity and reversal on stated domains |
| Theorem 1.4, Corollary 1.5, Remark 1.6 | Polynomial sector, full-generator spectral points at positive speed, sector incompleteness |
| Lemma 1.7, Remark 1.8 | Curvature bounds and exact mean curvature |
| Theorem 1.9 | Both concrete Hermite deficit identities on the real symmetric generator graph; first identity on the weak-H¹ domain |
| Theorem 1.10 | Both differential deficits with ordinary Schwartz derivatives and affine equality |
| Theorem 1.12 | Radial Ginibre log-Sobolev inequality and weak-domain completion |
| Theorem 1.13 | Gaussian matrix spectral law and overlap inequalities on finite-energy domains |
| Theorem 1.14 | Nonquadratic inequalities under the stated potential and observable hypotheses |
| Lemmas/Remarks 2.1–2.8 | Energy identity, maximal Gaussian derivative domain, equality space, canonical minimal dbar solver, entire-space closure, division and projection geometry |
| Generator and semigroup | Full diffusion, strongly continuous Markov semigroup and original-SDE identification |
| Lemmas A.1–A.3 | Weak-domain closure, graph-norm equivalence, global/collision-free core equality and zero collision capacity |
| Appendix B and supplementary results | Hermite formulas, linear statistics, counterexamples and Bochner/commutation identities |
| Problems 1.11, 1.15, 1.16; Appendix C | Open research questions and numerical experiments; not asserted solved or certified |

## Numbered paper coverage

The authoritative paper reference is Djalil Chafaï, *An optimal Poincaré inequality
for the complex Ginibre log-gas*, [arXiv:2608.19358v2](http://arxiv.org/abs/2608.19358v2). The numbered inventory
was checked against the official v2 full text linked from that page on 2026-10-07.
This is a source-to-endpoint inventory, not an independent audit of every proof.
“Verified” means a matching compiled result on the described domain; “support”
means related proved infrastructure, with the literal paper statement still to
be checked. Open research problems are not completion theorems.

### Introduction: every numbered statement

| Number | Statement | Status and Lean evidence |
| --- | --- | --- |
| [Theorem 1.1](http://arxiv.org/abs/2608.19358v2) | Optimal symmetric Poincaré inequality | Verified on the full symmetric weak-H¹ domain: `ginibre_symmetric_weak_poincare` in [GinibreSymmetricWeakPoincare](GinibrePoincare/Analysis/GinibreSymmetricWeakPoincare.lean). Center-of-mass attainment and exhaustive affine equality are proved; see [GinibreEqualityWeakAffine](GinibrePoincare/Analysis/GinibreEqualityWeakAffine.lean). Paper normalization is Var ≤ ½ E, E = (1/n)∫‖∇f‖². |
| [Theorem 1.2](http://arxiv.org/abs/2608.19358v2) | Equilibrium factorization | Verified: `equilibrium_probability_factorization`, `equilibrium_jointLaw`, `coordinateSum_recentered_indepFun` in [EquilibriumProbability](GinibrePoincare/Analysis/EquilibriumProbability.lean), plus the density and Gamma-radius laws. Coordinate sum is standard complex Gaussian and independent of the recentered configuration. |
| [Theorem 1.3](http://arxiv.org/abs/2608.19358v2) | Dynamical factorization | Verified on stated stochastic domains: original Brownian-driven process, independent center/relative processes and actual independent-driver CIR equations. `ginibreBrownian_full_two_radius_independent_CIR_realization` in [GinibreStochasticFullTwoRadiusRealization](GinibrePoincare/Analysis/GinibreStochasticFullTwoRadiusRealization.lean); joint realization requires n ≥ 2 and collision-free deterministic initial state. Random-initial independence uses independent center/relative initial projections. |
| [Theorem 1.4](http://arxiv.org/abs/2608.19358v2) | Polynomial eigenfunctions | Verified for n ≥ 2: `polynomialEigenfunction_eigenvalue_equation_atSpeed` in [PolynomialEigenfunctionGenerator](GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean), finite polynomial expansion in [PolynomialEigenfunctionBasis](GinibrePoincare/Analysis/PolynomialEigenfunctionBasis.lean), and equilibrium orthogonality. Full closed-sector basis and generator identification are also proved. |
| [Corollary 1.5](http://arxiv.org/abs/2608.19358v2) | Spectrum contains {−2αk/n : k ∈ ℕ} | Compiled for every n > 0 and positive paper speed α: `ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment` in [GinibreOneParticleSpectrum](GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean). Actual coordinate-sum powers supply nonzero eigenvectors; their squared norms are k!. Uses the actual full symmetric generator and the ordinary unbounded-operator spectrum, defined as absence of a bounded two-sided resolvent on its exact graph domain. This is not Mathlib’s bounded-operator algebra spectrum. The n = 1 case is included. |
| [Remark 1.6](http://arxiv.org/abs/2608.19358v2) | Polynomial-sector incompleteness | Verified: `polynomialSector_incomplete` in [PolynomialSectorIncompleteness](GinibrePoincare/Analysis/PolynomialSectorIncompleteness.lean), with a concrete nonzero centered quadratic orthogonal witness. |
| [Lemma 1.7](http://arxiv.org/abs/2608.19358v2) | Curvature has no lower bound | Verified for n ≥ 2: `ginibre_pointwise_bakry_emery_curvature_unbounded_below` in [GinibrePointwiseCurvature](GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean). This restriction follows the surrounding paper discussion; n = 1 is Gaussian. |
| [Remark 1.8](http://arxiv.org/abs/2608.19358v2) | Constant mean curvature | Verified: `ginibre_pointwise_mean_curvature` equals 2 for n > 0. The recentered curvature obstruction for n ≥ 2 is in [GinibrePointwiseCurvatureTangent](GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean). |
| [Theorem 1.9](http://arxiv.org/abs/2608.19358v2) | Hermite-series Poincaré and integrated Γ₂ deficits | Verified: `fullTheoremOneNine` in [FullTheoremOneNine](GinibrePoincare/Endgame/FullTheoremOneNine.lean), on the actual real symmetric generator graph. Exact remainder coefficients 2/4 and Hermite-tail coefficients 4/8; actual weak gradient and tail summability follow from graph membership. |
| [Theorem 1.10](http://arxiv.org/abs/2608.19358v2) | Differential sum-of-squares deficits | Verified on the stated generator graph: `fullTheoremOneTen` in [FullTheoremOneTen](GinibrePoincare/Endgame/FullTheoremOneTen.lean), on the actual real symmetric generator graph. Constructs v = N⁻¹ᐟ² proj(H⊥)(U f̃), derives its first and second weak Wirtinger derivatives from the actual Ginibre weak gradient, and proves both exact identities with coefficients 4/n and 8/n plus full affine equality. `ginibreDifferentialSecondEnergy_eq_integral` expresses the energy as literal Gaussian integrals of squared second derivatives. `fullTheoremOneTenSchwartz` now states the same endpoint with literal ordinary Lebesgue Schwartz distributional first and second derivatives; their equivalence to the independently defined weighted graph is proved. |
| [Problem 1.11](http://arxiv.org/abs/2608.19358v2) | Best symmetric log-Sobolev constant; is it 1? | Open research question. Radial LSI and matrix-overlap entropy bounds do not resolve unrestricted symmetric LSI. |
| [Theorem 1.12](http://arxiv.org/abs/2608.19358v2) | Uniform symmetric radial LSI | Verified on the smooth radial core and its Sobolev completion: `logSobolevInequality_instance` in [LogSobolevInequality](GinibrePoincare/Analysis/LogSobolevInequality.lean), `radial_sobolev_lsi` in [FullRadialLSIReduction](GinibrePoincare/Analysis/FullRadialLSIReduction.lean). Ent(f²) ≤ E. An old Lean comment calls this 1.10; arXiv v2 numbering is 1.12. |
| [Theorem 1.13](http://arxiv.org/abs/2608.19358v2) | Matrix lift and eigenvector-overlap inequalities | Verified: `fullMatrixLift_functional_inequalities` in [FullMatrixLift](GinibrePoincare/Endgame/FullMatrixLift.lean). Symmetric C¹ observable, actual Ginibre L² value and finite actual overlap energy; variance coefficient 2/n and entropy coefficient 4/n. |
| [Theorem 1.14](http://arxiv.org/abs/2608.19358v2) | Nonquadratic determinantal log-gases | Verified: `fullNonQuadraticPotentialTheorem` in [FullNonQuadraticPotential](GinibrePoincare/Endgame/FullNonQuadraticPotential.lean). Actual C² rotational potential, finite partition and ρ > 0. Smooth compact symmetric Poincaré under ΔV ≥ 2ρ with coefficient 1/(nρ); radial LSI under strong convexity with coefficient 2/(nρ). Bounded Lipschitz radial extension is separately proved. |
| [Problem 1.15](http://arxiv.org/abs/2608.19358v2) | Arbitrary inverse temperatures | Open research question; the β = 2 determinantal proofs do not solve it. |
| [Problem 1.16](http://arxiv.org/abs/2608.19358v2) | Higher-dimensional log-gases | Open research question; the planar Ginibre results do not solve it. |

### Proof lemmas and remarks

| Number | Statement | Status and Lean evidence |
| --- | --- | --- |
| [Lemma 2.1](http://arxiv.org/abs/2608.19358v2) | Dirichlet form under Vandermonde transform | Verified normalized identity: `groundStateEnergyIdentity` in [GroundStateDbar](GinibrePoincare/Analysis/GroundStateDbar.lean), preserving the factor 4. |
| [Lemma 2.2](http://arxiv.org/abs/2608.19358v2) | Gaussian dbar spectral gap | Verified on the actual entire-function space: `gaussianDbarEstimateStatement` and `gaussianHolomorphicDistanceSq_eq_projectionNorm` in [GaussianEntireDistance](GinibrePoincare/Analysis/GaussianEntireDistance.lean), with maximal ordinary Schwartz-domain extensions in [GaussianDbarWeakEquality](GinibrePoincare/Analysis/GaussianDbarWeakEquality.lean). |
| [Remark 2.3](http://arxiv.org/abs/2608.19358v2) | Weak dbar domain and Gaussian equality cases | Compiled on the maximal ordinary Schwartz Gaussian L² derivative domain. [GaussianDbarCompactCore](GinibrePoincare/Analysis/GaussianDbarCompactCore.lean) proves compact C∞ graph density. [GaussianDbarWeakEquality](GinibrePoincare/Analysis/GaussianDbarWeakEquality.lean) proves the sharp gap, exact mode criterion and compact smooth equality iff zero. [GaussianDbarEqualitySpace](GinibrePoincare/Analysis/GaussianDbarEqualitySpace.lean) proves the closed direct sum of degrees zero and one, convergent coefficient expansions with exact ℓ² norm, and unconditional derivative-domain membership/attainment for each equality-space vector. Exact pointwise creation formula (2.19) is in [GaussianFirstModeCreation](GinibrePoincare/Analysis/GaussianFirstModeCreation.lean). |
| [Remark 2.4](http://arxiv.org/abs/2608.19358v2) | Hörmander–Berndtsson closed-form solvability | Compiled literal arbitrary-form existence: `gaussianVolumeClosedFormSolvability` in [GaussianClosedFormVolume](GinibrePoincare/Analysis/GaussianClosedFormVolume.lean). Every ordinary distributionally closed Gaussian L² (0,1)-form has an actual L² solution of each ordinary volume derivative equation, with squared norm ≤ n⁻¹ times the sum of component squared norms. The coefficient candidate and bound are derived from compact tests, not assumed. Canonical solution, uniqueness and minimal norm: `gaussianVolumeClosedForm_canonicalSolvability` in [GaussianCanonicalDbarSolution](GinibrePoincare/Analysis/GaussianCanonicalDbarSolution.lean). |
| [Remark 2.5](http://arxiv.org/abs/2608.19358v2) | Closedness of the entire-function Bargmann–Fock space | Compiled literal entire L² space identification and closedness: `gaussianEntireL2_eq_zeroModeClosedSpan`, `isClosed_gaussianEntireL2` in [GaussianEntireSpaceClosure](GinibrePoincare/Analysis/GaussianEntireSpaceClosure.lean). The same module proves a local pointwise estimate and `gaussianEntireRepresentative_tendstoLocallyUniformly` for arbitrary L²-convergent actual entire representatives. Multivariate entire regularity and actual infinite-series reconstruction are derived in focused modules, not assumed. |
| [Lemma 2.6](http://arxiv.org/abs/2608.19358v2) | Alternating holomorphic Vandermonde divisibility | Verified for arbitrary entire functions across all collisions: `entire_alternating_vandermonde_factorization` in [EntireVandermondeFactorization](GinibrePoincare/Analysis/EntireVandermondeFactorization.lean). The quotient is entire and symmetric. Actual Gaussian L² representative counterpart is exported in the same module. |
| [Lemma 2.7](http://arxiv.org/abs/2608.19358v2) | Holomorphic–antiholomorphic projection geometry | Verified for the actual entire symmetric L² space in [GinibreEntireProjectionGeometry](GinibrePoincare/Analysis/GinibreEntireProjectionGeometry.lean): centered orthogonality, arbitrary complex two-projection bound and real centered Pythagoras/half-distance (2.26–2.28). [GinibreEntireProjectionDistance](GinibrePoincare/Analysis/GinibreEntireProjectionDistance.lean) proves literal representative infima and attainment. [GaussianGinibreProjectionIntertwining](GinibrePoincare/Analysis/GaussianGinibreProjectionIntertwining.lean) proves (2.23) with the exact unnormalized mass factor. |
| [Remark 2.8](http://arxiv.org/abs/2608.19358v2) | Equality cases in the two estimates | Compiled explicit center decomposition, Vandermonde translation invariance and derivative cancellation in [GinibreCenterProjectionEquality](GinibrePoincare/Analysis/GinibreCenterProjectionEquality.lean). Actual center projection = S/2 and exact half-distance equality in [GinibreCenterProjectionClasses](GinibrePoincare/Analysis/GinibreCenterProjectionClasses.lean). Gaussian zero projection, weak derivatives, exact gap equality and first antiholomorphic Hermite-space membership for the normalized V·conjugate(S) are in [GinibreCenterProjectionGaussian](GinibrePoincare/Analysis/GinibreCenterProjectionGaussian.lean); the pointwise correction sum is stated unnormalized. |

Sections 3–7 contain alternative proofs and proof calculations but no additional
numbered theorem environments. The status above tracks their conclusions; it
does not claim every alternative proof has an independently exported Lean route.

### Appendices

| Number / section | Statement | Status and Lean evidence |
| --- | --- | --- |
| [Lemma A.1](http://arxiv.org/abs/2608.19358v2) | Domain of the closed gradient | Proved uniqueness and closed weak graph in [GinibreWeakGradient](GinibrePoincare/Analysis/GinibreWeakGradient.lean), plus actual weak-pair core approximation in [GinibreArbitraryWeakPairClosure](GinibrePoincare/Analysis/GinibreArbitraryWeakPairClosure.lean). |
| [Lemma A.2](http://arxiv.org/abs/2608.19358v2) | Equivalent graph norms and collision-free core closure | Compiled actual positive-speed norm comparison: `ginibre_gradient_graph_norm_equivalence` in [GinibreGraphNormEquivalence](GinibrePoincare/Analysis/GinibreGraphNormEquivalence.lean), with factors √min(1,c) and √max(1,c), c = αₙ/βₙ > 0. Collision cutoff approximation is proved in [GinibreCollisionCutoffSobolevApproximation](GinibrePoincare/Analysis/GinibreCollisionCutoffSobolevApproximation.lean). Actual nonsymmetric real global/interior compact smooth gradient graph closures are now equal to the independently defined distributional graph: `ginibreRealInteriorCore_closure_eq_distributional` and `ginibreRealSmoothCore_closure_equivalence` in [GinibreRealCoreClosureEquivalence](GinibrePoincare/Analysis/GinibreRealCoreClosureEquivalence.lean), compiled and audited. The literal complex-valued global/collision-free smooth-core closure equality is now compiled: `ginibreComplexSmoothCore_closure_equivalence` in [GinibreComplexCoreClosureEquivalence](GinibrePoincare/Analysis/GinibreComplexCoreClosureEquivalence.lean), with actual complex L² values and Euclidean complex gradients defined by the real Fréchet derivative in each coordinate; only standard axioms occur. |
| [Lemma A.3](http://arxiv.org/abs/2608.19358v2) | Collision set has zero capacity | Verified: `ginibreCollisionSet_capacity_zero` in [GinibreCollisionCapacity](GinibrePoincare/Analysis/GinibreCollisionCapacity.lean), for the literal weighted weak-H¹ capacity, n > 0. |
| Appendix B | Hermite orthogonal polynomials | No numbered theorem environments. Normalized basis, completeness, Parseval, Rodrigues and both Wirtinger lowering relations are proved; [HermiteRodriguesMultivariate](GinibrePoincare/Analysis/HermiteRodriguesMultivariate.lean) and [HermiteRodriguesHolomorphicLowering](GinibrePoincare/Analysis/HermiteRodriguesHolomorphicLowering.lean). |
| Appendix C | Numerical experiments | No numbered theorem environments or proof obligation. Numerical experiments are not certified by the Lean theorem audits. |

## Final analytic correspondence

The [official v2 proof section](https://arxiv.org/html/2608.19358v2#S2) was checked against the endpoints. Remarks 2.3–2.5 have the full ordinary distributional domain, compact smooth core, equality space, canonical minimal solver and actual entire-space closedness/local uniform convergence. Lemma 2.6 has global entire quotient existence. Lemma 2.7 has actual entire-space geometry and representative distances. Remark 2.8 has exact center projection and Gaussian first-mode/gap equalities. `groundStateDistanceIdentityStatement` and `ginibreHalfDistanceStatement` apply to the full smooth compact symmetric core, including collision points. `fullMainAnalyticProof` supplies all five previously abstract analytic inputs with proved concrete theorems.

## Open work and next step

No listed asserted-result formalization gap remains. Problems 1.11, 1.15 and 1.16 remain open research questions, and Appendix C experiments are not numerically certified. Each alternative proof route is not independently exported. Review the completed source and numbered correspondence; no overall completion percentage is assigned.

## Scope qualifications

Theorems 1.9 and 1.10 use the actual real symmetric generator graph. The differential theorem now also has a literal ordinary Schwartz distributional endpoint, proved equivalent to the independent weighted compact-test graph. Sharp equality is
classified on the full symmetric weak domain. Matrix inequalities require actual
L² values and finite overlap energy. Nonquadratic inequalities use the stated
potential hypotheses and smooth compact symmetric observables, with a radial
restriction for log-Sobolev. Joint two-radius CIR realization is for n ≥ 2 and
deterministic collision-free initial configurations. Stochastic invariance and
analytic semigroup identification cover n > 0 and every nonnegative speed and
horizon.

The numbered inventory records statement correspondence; the axiom audits separately verify compilation and permitted axiom usage. They are not an independent mathematical peer review of every definition or proof.

## Build and audit evidence

Fresh `LEAN_NUM_THREADS=1 make check` passed: 5,384 build jobs; 1,296 original modules assigned exactly once to twelve subprojects; all 1,308 library modules publicly imported; only the authorized independent Challenge hole; 5,079 public axiom queries; all-local audit of 11,112 declarations including private helpers. Only `propext`, `Classical.choice` and `Quot.sound` occur in the proof-library/Solution audit closure. Both root compatibility files compile. Actual Comparator passes with empty `definition_names`, so concrete definitions remain recursively compared; con-ron accepts 61,907 exported declarations, and nanoda and Lean’s default kernel also accept.

- [Full build, inventory, source and axiom audits](ginibre-upgrade-verified-check.log)
- [Import compatibility](ginibre-upgrade-compatibility.log)
- [Draft compatibility](ginibre-upgrade-drafts.log)
- [Actual strict Comparator and three kernel checks](ginibre-upgrade-comparator.log)
- [Offline Palomar structural preflight](ginibre-upgrade-preflight.log)

Compilation and axiom audits establish source coverage and soundness relative to the permitted axioms. The numbered inventory above separately records statement correspondence and natural domain qualifications.

## Lean source counts

Refreshed using `python3 scripts/count_lean_sources.py` at this checkpoint.

| Source scope | Files/modules | Physical lines |
| --- | ---: | ---: |
| Active project Lean sources, including roots and generated facades | 1,315 | 142,364 |
| Transitively imported Mathlib | 3,794 | 1,251,826 |
| Project plus imported Mathlib | 5,109 | 1,394,190 |

Comments and blank lines are included. Each imported Mathlib module is counted
once in full. Archives, Lean core and other dependencies are excluded. This is
module-level usage, not declaration-level proof dependency usage. The subproject
inventory counts original library files only, excluding its generated facades and
root audit/compatibility files.

## Final assembly and repository state

The original analytic main proof, both Hermite deficits and both differential deficits are exported and audited. Generator membership and actual derivative-domain theorems supply the analytic facts; none remains a completion assumption. Corollary 1.5 covers every positive dimension and positive speed. Appendix A.2 includes actual graph-norm comparison and real/complex global versus collision-free core equality.

The user-authorized fresh Git snapshot includes the final proofs, thematic subprojects, reports, pinned dependency manifest and verification logs. Previous Git metadata is preserved at `/tmp/ginibre-git-before-reinit-2026-10-07/repository.git`. No remote publication or additional Mathlib checkout was performed. The final v4.35.0-rc2 build and audits above supersede earlier checkpoints preserved in STATUS.md.
