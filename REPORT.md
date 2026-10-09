# Ginibre Poincaré formalization report

Updated on 2026-10-09 with the human readability revision; mathematical
correspondence findings below remain the 2026-10-08 review.

Paper authority: Djalil Chafaï, *An optimal Poincaré inequality for the complex
Ginibre log-gas*, [arXiv:2608.19358v2](https://arxiv.org/html/2608.19358v2).
Local TeX is not the statement authority.

The original analytic Theorem 1.1 proof, both requested independent spectral
and Hermite–Slater routes, the integrated Bochner–Kodaira route and the primary
Bakry–Émery radial route are exported. The new correspondence endpoints close
the former matrix H¹, literal pointwise Γ₂, unrestricted operator/dynamics,
Section 6 spectral-calculus and auxiliary-assertion gaps. See
[FullPaper](GinibrePoincare/Endgame/FullPaper.lean),
[CorrespondenceEndpoints](GinibrePoincare/Endgame/CorrespondenceEndpoints.lean)
and [STATUS.md](STATUS.md) for precise verification evidence.

Problems 1.11, 1.15 and 1.16 remain open research questions; Appendix C numerical
experiments are outside theorem certification. No overall completion percentage
is assigned.

## Human readability revision

The [reading index](HUMAN_READABILITY.md) and four topic guides give ordered
routes from definitions through the main arguments to the paper endpoints,
including ordinary weak domains, generator graphs, stochastic localization,
matrix overlaps, nonquadratic potentials and Appendices A–B. Eighty-two Lean
modules have revised mathematical explanations or declaration documentation.
Proof-local names now identify important coefficient, convergence and driver
facts in the revised arguments.

Seven named result records expose the existing conclusions of Theorems 1.9
and 1.10, the matrix inequalities, maximal-domain Gaussian Bochner identity,
and relative-radius stopped CIR realization. Five proved adapters construct
these interfaces; existing theorem names and statements remain available.
The differential deficit and pointwise Γ₂ proofs now use the named deficit
fields. No mathematical proof route or endpoint domain is changed.

Conservative comma and binder-colon spacing was applied to 844 modules. The
formatter deliberately preserves compound mathematical notation and skips
syntax-defining files. `make readability` checks this policy and its regression
cases. It does not claim conformance to every Mathlib style convention.

The [statement comparison](verification/readability-statement-check.json)
inspects 3,490 existing declarations in 896 edited Lean files: no signatures
changed after ignoring comments and whitespace, and no declarations were
removed. This source comparison complements the kernel build and axiom audits;
it is not a new paper-correspondence review. Technical helper modules outside
the documented routes have not all received individual mathematical editorial
reviews. The [status dashboard](STATUS.md) and [verification record](verification/readability-final-check.txt) record the passing build and audits, refreshed views and browser-check limitation.

## Independent full-paper correspondence review

The initial review at `0779d08` identified substantive gaps. The independent
[main follow-up](verification/correspondence-main-followup.md) and
[extension/dynamics follow-up](verification/correspondence-extensions-followup.md)
now inspect the actual new measures, domains and operators and find no remaining
concrete conclusion gap in their combined paper inventory. This statement review
is separate from the full-tree build/axiom checks and external publication.
[CORRESPONDENCE_REVIEW.md](CORRESPONDENCE_REVIEW.md) records the exact disposition
of historical findings and the source qualifications.

Domain qualifications are preserved: real GUE uses the paper's smooth compact
H¹ completion; local Dolbeault exactness covers ordinary locally L² coefficients
on arbitrary open sets in every dimension; general real Brascamp–Lieb covers C²
potentials with everywhere positive-definite Hessian, finite Gibbs mass, and
locally Lipschitz or ordinary local weak-gradient observables with finite actual
inverse-Hessian energy. No uniform Hessian lower bound or global gradient-L²
hypothesis is added. The latter contextual theorem uses the precise classical
statement in the primary Carlen–Cordero-Erausquin–Lieb (2013) source; an exact
reconstruction of the inaccessible 1976 proof is not claimed. Introductory
physical applications are represented by the actual density, antisymmetry and
normalized Slater identities, without inventing unspecified external models.

[Live registry checks](verification/registry-publication-check.md) confirm
PALOMAR-2026-10-09-000001 v1 publication for the earlier immutable Theorem 1.1
comparison snapshot. This receipt does not certify every paper endpoint or the
current readability revision.

## Historical Palomar mechanical checkpoint

Lean and the existing Mathlib checkout are upgraded together to v4.35.0-rc2. The final single-thread full build, source audit, 5,079 public axiom queries, 11,112-declaration all-local audit and both root compatibility checks pass. Actual Comparator passes strict recursive statement comparison and all three kernels: con-ron, nanoda and Lean’s default kernel. The independent Challenge has exactly the user-authorized statement hole; the proof library and Solution remain hole-free and use only the three permitted standard axioms. The comparison covers full symmetric weak-H¹ Theorem 1.1 and exhaustive affine equality, not the whole paper. Offline preflight reports zero blockers and metadata passes the official v0.4 schema. Palomar accepted submission `7fh68vzqfjeu` at the immutable commit
`fb58b4fd765f19a65c46cb82fb647fb0d94e28ca`; its official mechanical
verification passed. See [PALOMAR.md](PALOMAR.md) for the recorded editorial
review and registration status.

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
“Verified” records compiled endpoint coverage on the described domain; the
2026-10-08 independent follow-up review checks actual definitions and stated
domains. The literal pointwise Γ₂ integral is now identified independently of
the operator-norm encoding. “Support”
means related proved infrastructure, with the literal paper statement still to
be checked. Open research problems are not completion theorems.

### Introduction: every numbered statement

| Number | Statement | Status and Lean evidence |
| --- | --- | --- |
| [Theorem 1.1](http://arxiv.org/abs/2608.19358v2) | Optimal symmetric Poincaré inequality | Verified on the full symmetric weak-H¹ domain: `ginibre_symmetric_weak_poincare` in [GinibreSymmetricWeakPoincare](GinibrePoincare/Analysis/GinibreSymmetricWeakPoincare.lean). Center-of-mass attainment and exhaustive affine equality are proved; see [GinibreEqualityWeakAffine](GinibrePoincare/Analysis/GinibreEqualityWeakAffine.lean). Paper normalization is Var ≤ ½ E, E = (1/n)∫‖∇f‖². |
| [Theorem 1.2](http://arxiv.org/abs/2608.19358v2) | Equilibrium factorization | Verified: `equilibrium_probability_factorization`, `equilibrium_jointLaw`, `coordinateSum_recentered_indepFun` in [EquilibriumProbability](GinibrePoincare/Analysis/EquilibriumProbability.lean), plus the density and Gamma-radius laws. Coordinate sum is standard complex Gaussian and independent of the recentered configuration. |
| [Theorem 1.3](http://arxiv.org/abs/2608.19358v2) | Dynamical factorization | Compiled factorization and actual unstopped independent-driver CIR equations in [CorrespondenceDynamicsGlobalCIR](GinibrePoincare/Analysis/CorrespondenceDynamicsGlobalCIR.lean). Original Brownian-driven process and independent center/relative processes are constructed. `ginibreBrownian_full_two_radius_independent_CIR_realization` in [GinibreStochasticFullTwoRadiusRealization](GinibrePoincare/Analysis/GinibreStochasticFullTwoRadiusRealization.lean); joint realization requires n ≥ 2 and collision-free deterministic initial state. Random-initial independence uses independent center/relative initial projections. |
| [Theorem 1.4](http://arxiv.org/abs/2608.19358v2) | Polynomial eigenfunctions | Verified for n ≥ 2: `polynomialEigenfunction_eigenvalue_equation_atSpeed` in [PolynomialEigenfunctionGenerator](GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean), finite polynomial expansion in [PolynomialEigenfunctionBasis](GinibrePoincare/Analysis/PolynomialEigenfunctionBasis.lean), and equilibrium orthogonality. Full closed-sector basis and generator identification are also proved. |
| [Corollary 1.5](http://arxiv.org/abs/2608.19358v2) | Spectrum contains {−2αk/n : k ∈ ℕ} | Compiled for every n > 0 and positive paper speed α: `ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment` in [GinibreOneParticleSpectrum](GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean). Actual coordinate-sum powers supply nonzero eigenvectors; their squared norms are k!. Uses the actual full symmetric generator and the ordinary unbounded-operator spectrum, defined as absence of a bounded two-sided resolvent on its exact graph domain. This is not Mathlib’s bounded-operator algebra spectrum. The n = 1 case is included. |
| [Remark 1.6](http://arxiv.org/abs/2608.19358v2) | Polynomial-sector incompleteness | Verified: `polynomialSector_incomplete` in [PolynomialSectorIncompleteness](GinibrePoincare/Analysis/PolynomialSectorIncompleteness.lean), with a concrete nonzero centered quadratic orthogonal witness. |
| [Lemma 1.7](http://arxiv.org/abs/2608.19358v2) | Curvature has no lower bound | Verified for n ≥ 2: `ginibre_pointwise_bakry_emery_curvature_unbounded_below` in [GinibrePointwiseCurvature](GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean). This restriction follows the surrounding paper discussion; n = 1 is Gaussian. |
| [Remark 1.8](http://arxiv.org/abs/2608.19358v2) | Constant mean curvature | Verified: `ginibre_pointwise_mean_curvature` equals 2 for n > 0. The recentered curvature obstruction for n ≥ 2 is in [GinibrePointwiseCurvatureTangent](GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean). |
| [Theorem 1.9](http://arxiv.org/abs/2608.19358v2) | Hermite-series Poincaré and integrated Γ₂ deficits | Compiled operator-graph and literal integrated pointwise Γ₂ identities in [FullTheoremOneNinePointwiseGamma](GinibrePoincare/Endgame/FullTheoremOneNinePointwiseGamma.lean): `fullTheoremOneNine` in [FullTheoremOneNine](GinibrePoincare/Endgame/FullTheoremOneNine.lean), on the actual real symmetric generator graph. Exact remainder coefficients 2/4 and Hermite-tail coefficients 4/8; actual weak gradient and tail summability follow from graph membership. |
| [Theorem 1.10](http://arxiv.org/abs/2608.19358v2) | Differential sum-of-squares deficits | Compiled differential identities on the symmetric generator graph, with the literal pointwise Γ₂ bridge in [CorrespondenceOperatorUnrestrictedGamma](GinibrePoincare/Analysis/CorrespondenceOperatorUnrestrictedGamma.lean): `fullTheoremOneTen` in [FullTheoremOneTen](GinibrePoincare/Endgame/FullTheoremOneTen.lean), on the actual real symmetric generator graph. Constructs v = N⁻¹ᐟ² proj(H⊥)(U f̃), derives its first and second weak Wirtinger derivatives from the actual Ginibre weak gradient, and proves both exact identities with coefficients 4/n and 8/n plus full affine equality. `ginibreDifferentialSecondEnergy_eq_integral` expresses the energy as literal Gaussian integrals of squared second derivatives. `fullTheoremOneTenSchwartz` now states the same endpoint with literal ordinary Lebesgue Schwartz distributional first and second derivatives; their equivalence to the independently defined weighted graph is proved. |
| [Problem 1.11](http://arxiv.org/abs/2608.19358v2) | Best symmetric log-Sobolev constant; is it 1? | Open research question. Radial LSI and matrix-overlap entropy bounds do not resolve unrestricted symmetric LSI. |
| [Theorem 1.12](http://arxiv.org/abs/2608.19358v2) | Uniform symmetric radial LSI | Verified on the smooth radial core and its Sobolev completion: `logSobolevInequality_instance` in [LogSobolevInequality](GinibrePoincare/Analysis/LogSobolevInequality.lean), `radial_sobolev_lsi` in [FullRadialLSIReduction](GinibrePoincare/Analysis/FullRadialLSIReduction.lean). Ent(f²) ≤ E. An old Lean comment calls this 1.10; arXiv v2 numbering is 1.12. |
| [Theorem 1.13](http://arxiv.org/abs/2608.19358v2) | Matrix lift and eigenvector-overlap inequalities | `correspondenceMatrix_theorem_1_13` in [CorrespondenceMatrixWeakClosure](GinibrePoincare/Analysis/CorrespondenceMatrixWeakClosure.lean): symmetric C¹ observable with literal Gaussian matrix H¹ lift. The actual weak spectral derivative and finite overlap energy are proved internally, with variance coefficient 2/n and entropy coefficient 4/n. The earlier finite-overlap endpoint remains exported in [FullMatrixLift](GinibrePoincare/Endgame/FullMatrixLift.lean). |
| [Theorem 1.14](http://arxiv.org/abs/2608.19358v2) | Nonquadratic determinantal log-gases | Verified: `fullNonQuadraticPotentialTheorem` in [FullNonQuadraticPotential](GinibrePoincare/Endgame/FullNonQuadraticPotential.lean). Actual C² rotational potential, finite partition and ρ > 0. Smooth compact symmetric Poincaré under ΔV ≥ 2ρ with coefficient 1/(nρ); radial LSI under strong convexity with coefficient 2/(nρ). Bounded Lipschitz radial extension is separately proved. |
| [Problem 1.15](http://arxiv.org/abs/2608.19358v2) | Arbitrary inverse temperatures | Open research question; the β = 2 determinantal proofs do not solve it. |
| [Problem 1.16](http://arxiv.org/abs/2608.19358v2) | Higher-dimensional log-gases | Open research question; the planar Ginibre results do not solve it. |

### Proof lemmas and remarks

| Number | Statement | Status and Lean evidence |
| --- | --- | --- |
| [Lemma 2.1](http://arxiv.org/abs/2608.19358v2) | Dirichlet form under Vandermonde transform | Verified normalized identity: `groundStateEnergyIdentity` in [GroundStateDbar](GinibrePoincare/Analysis/GroundStateDbar.lean), preserving the factor 4. |
| [Lemma 2.2](http://arxiv.org/abs/2608.19358v2) | Gaussian dbar spectral gap | Verified on the actual entire-function space: `gaussianDbarEstimateStatement` and `gaussianHolomorphicDistanceSq_eq_projectionNorm` in [GaussianEntireDistance](GinibrePoincare/Analysis/GaussianEntireDistance.lean), with maximal ordinary Schwartz-domain extensions in [GaussianDbarWeakEquality](GinibrePoincare/Analysis/GaussianDbarWeakEquality.lean). |
| [Remark 2.3](http://arxiv.org/abs/2608.19358v2) | Weak dbar domain and Gaussian equality cases | Compiled on the maximal ordinary Schwartz Gaussian L² derivative domain. [GaussianDbarCompactCore](GinibrePoincare/Analysis/GaussianDbarCompactCore.lean) proves compact C∞ graph density. [GaussianDbarWeakEquality](GinibrePoincare/Analysis/GaussianDbarWeakEquality.lean) proves the sharp gap, exact mode criterion and compact smooth equality iff zero. [GaussianDbarEqualitySpace](GinibrePoincare/Analysis/GaussianDbarEqualitySpace.lean) proves the closed direct sum of degrees zero and one, convergent coefficient expansions with exact ℓ² norm, and unconditional derivative-domain membership/attainment for each equality-space vector. Real analyticity of every equality vector is proved in [CorrespondenceAuxiliaryEqualityAnalytic](GinibrePoincare/Analysis/CorrespondenceAuxiliaryEqualityAnalytic.lean). Exact pointwise creation formula (2.19) is in [GaussianFirstModeCreation](GinibrePoincare/Analysis/GaussianFirstModeCreation.lean). |
| [Remark 2.4](http://arxiv.org/abs/2608.19358v2) | Hörmander–Berndtsson closed-form solvability | Compiled literal arbitrary-form existence: `gaussianVolumeClosedFormSolvability` in [GaussianClosedFormVolume](GinibrePoincare/Analysis/GaussianClosedFormVolume.lean). Every ordinary distributionally closed Gaussian L² (0,1)-form has an actual L² solution of each ordinary volume derivative equation, with squared norm ≤ n⁻¹ times the sum of component squared norms. The coefficient candidate and bound are derived from compact tests, not assumed. Canonical solution, uniqueness and minimal norm: `gaussianVolumeClosedForm_canonicalSolvability` in [GaussianCanonicalDbarSolution](GinibrePoincare/Analysis/GaussianCanonicalDbarSolution.lean). |
| [Remark 2.5](http://arxiv.org/abs/2608.19358v2) | Closedness of the entire-function Bargmann–Fock space | Compiled literal entire L² space identification and closedness: `gaussianEntireL2_eq_zeroModeClosedSpan`, `isClosed_gaussianEntireL2` in [GaussianEntireSpaceClosure](GinibrePoincare/Analysis/GaussianEntireSpaceClosure.lean). The same module proves a local pointwise estimate and `gaussianEntireRepresentative_tendstoLocallyUniformly` for arbitrary L²-convergent actual entire representatives. Multivariate entire regularity and actual infinite-series reconstruction are derived in focused modules, not assumed. Arbitrary measurable weights bounded positively on each compact are covered by [CorrespondenceAuxiliaryPositiveWeightClosure](GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveWeightClosure.lean) and [CorrespondenceAuxiliaryPositiveWeightUniform](GinibrePoincare/Analysis/CorrespondenceAuxiliaryPositiveWeightUniform.lean), including actual locally uniform convergence. |
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
| Appendix B | Hermite orthogonal polynomials | No numbered theorem environments. Normalized basis, completeness, Parseval, Rodrigues and both Wirtinger lowering relations are proved; literal Gram–Schmidt and leading-coefficient assertions are proved in [CorrespondenceAuxiliaryTensorGramSchmidt](GinibrePoincare/Analysis/CorrespondenceAuxiliaryTensorGramSchmidt.lean), [Leading](GinibrePoincare/Analysis/CorrespondenceAuxiliaryHermiteLeading.lean) and [TensorExpansion](GinibrePoincare/Analysis/CorrespondenceAuxiliaryTensorExpansion.lean);  [HermiteRodriguesMultivariate](GinibrePoincare/Analysis/HermiteRodriguesMultivariate.lean) and [HermiteRodriguesHolomorphicLowering](GinibrePoincare/Analysis/HermiteRodriguesHolomorphicLowering.lean). |
| Appendix C | Numerical experiments | No numbered theorem environments or proof obligation. Numerical experiments are not certified by the Lean theorem audits. |

## Compiled analytic endpoints and correspondence qualifications

The [official v2 proof section](https://arxiv.org/html/2608.19358v2#S2) was used to locate the following compiled endpoints. The independent follow-up review resolves equality-vector analyticity, arbitrary-weight closedness/local uniform convergence and the identified auxiliary assertions; its exact domains are recorded above. Remarks 2.3–2.5 have the full ordinary distributional domain, compact smooth core, equality space, canonical minimal solver and actual entire-space closedness/local uniform convergence. Lemma 2.6 has global entire quotient existence. Lemma 2.7 has actual entire-space geometry and representative distances. Remark 2.8 has exact center projection and Gaussian first-mode/gap equalities. `groundStateDistanceIdentityStatement` and `ginibreHalfDistanceStatement` apply to the full smooth compact symmetric core, including collision points. `fullMainAnalyticProof` supplies all five previously abstract analytic inputs with proved concrete theorems.

## Open work and next step

No remaining concrete mathematical conclusion gap was located in the combined
independent follow-up inventory. Full-tree verification and publication have
separate evidence in STATUS.md and PALOMAR.md. Palomar v1 is publicly registered for the earlier Theorem 1.1 snapshot; the
current revision has passed exact-commit preflight and official verification.
Submission `9nfa8zoiz8te` awaits review/status service recovery (HTTP 500) and
new-version registration. The open research Problems and numerical experiments retain
the exclusions stated above.

## Proof-route correspondence remarks

### Independent proof routes and domain qualifications

Result coverage and proof-route coverage are separate claims. The numbered
inventory records compiled endpoints for the asserted results; it does not mean
that every argument in the paper has a separate Lean implementation. The user requested independent implementations of four groups of routes on
2026-10-08. Their current correspondence evidence is recorded below. Compiled
ingredients are distinguished from complete concrete endpoints. The later table
records other original arguments replaced at existing endpoints.

| Requested route | Current Lean implementation | Completion restriction |
| --- | --- | --- |
| Theorem 1.1, Section 3 spectral route | [AlternativeSpectralPoincare](GinibrePoincare/Analysis/AlternativeSpectralPoincare.lean): concrete number forms, anti-Vandermonde factor, two-sided form identity, independently assembled sharp inequality; [DifferentialFactorization](GinibrePoincare/Analysis/AlternativeSpectralDifferentialFactorization.lean) proves literal complex pregenerator factorization (3.1) and Vandermonde calculations (3.3–3.4); [SpectralSupport](GinibrePoincare/Analysis/AlternativeSpectralSupport.lean) proves the actual full complex graph-spectrum support | Full symmetric ordinary weak-H¹ endpoint; literal generator spectrum in `{0} ∪ (−∞,−2]`, at paper speed |
| Theorem 1.1, Section 4 Hermite–Slater route | [AlternativeSlaterExpansion](GinibrePoincare/Analysis/AlternativeSlaterExpansion.lean) and [AlternativeSlaterPoincare](GinibrePoincare/Analysis/AlternativeSlaterPoincare.lean): actual determinant representatives, convergent ordered-frame expansion and factorial-normalized Parseval, degree energy and sharp inequality | Full symmetric ordinary weak-H¹ endpoint; signed orbit pairings, orthogonality, lowering and polynomial quotient proved; [Eigenfunctions](GinibrePoincare/Analysis/AlternativeSlaterEigenfunctions.lean) additionally exports literal (4.2) and homogeneous quotient degree (4.6) |
| Theorem 1.10, Section 6 integrated Bochner–Kodaira route | [AlternativeBochnerKodairaDifferential](GinibrePoincare/Analysis/AlternativeBochnerKodairaDifferential.lean), [Compact](GinibrePoincare/Analysis/AlternativeBochnerKodairaCompact.lean), [Closure](GinibrePoincare/Analysis/AlternativeBochnerKodairaClosure.lean): actual commutator, Gaussian IBP integrated identity and closed compact-jet extension | Focused compiled full real symmetric generator endpoint in [BochnerKodairaTheoremOneTen](GinibrePoincare/Endgame/BochnerKodairaTheoremOneTen.lean), with actual first/second weak derivatives and both exact deficits; full build and public/private audits pass |
| Theorem 1.14, primary Bakry–Émery radial LSI route | [ConvexGibbsLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryConvexGibbsLSI.lean) constructs Brownian noise and proves actual strongly convex Gibbs LSI; [LiftLSILimit](GinibrePoincare/Analysis/AlternativeBakryEmeryLiftLSILimit.lean), [RadialLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryRadialLSI.lean), [RadialProductLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryRadialProductLSI.lean) and [PotentialRadialLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLSI.lean) prove regularization, exact radius laws, entropy tensorization and interacting radial transfer | Exact `2/(nρ)` ordinary gradient coefficient; paper smooth compact radial domain and bounded Lipschitz radial extension. No supplied Brownian process, stationarity or analytic completion input; the endgame invokes this route |
| Theorem 1.13, Gaussian matrix Poincaré route | [SquareEntropyLinearization](GinibrePoincare/Analysis/SquareEntropyLinearization.lean), [MatrixGaussianPoincare](GinibrePoincare/Analysis/MatrixGaussianPoincare.lean), [AlternativeMatrixPoincare](GinibrePoincare/Analysis/AlternativeMatrixPoincare.lean): actual Gaussian matrix H¹ inequality, spectral pushforward and exact overlap energy, with finite-overlap H¹ membership derived internally | Exact coefficient `2/n`; full build and public/private audits pass. The endgame now invokes this Gaussian route |

| Paper proof argument | Lean route at the recorded endpoint |
| --- | --- |
| Theorem 1.14: primary Bakry–Émery radial LSI argument | Original Euclidean-lift route now formalized, with an expanded proof of the cited strongly convex Gibbs ingredient. The independent contracting Gaussian quantile transport proof remains exported |
| Theorem 1.3: joint quadratic variation and Lévy characterization of radial Brownian drivers | Discrete Brownian sums and limits, followed by independence through measurable functionals of independent paths |
| Lemma 2.6: Weierstrass division and holomorphic germs | Integral division by successive collision hyperplanes |
| Remark 2.4: invocation of Hörmander–Berndtsson solvability | Gaussian-specific Hermite spectral solver and projection to the canonical minimal solution |
| Theorem 1.2: polar-coordinate calculation of the recentered Gamma law | Sublevel-set scaling of a homogeneous weighted measure |
| Lemma 1.7: isolated colliding-pair curvature witness | Explicit configurations with all particles approaching one another |
| Dynamics: general diffusion/Hunt-process correspondence | Riesz resolvent, functional-calculus semigroup and direct original-SDE resolvent comparison |

The separate Section 3 spectral and Section 4 Hermite–Slater sharp weak-domain
endpoints are now implemented as described above; this does not certify every
calculation or argument in Sections 3–7. The original Section 2 analytic proof of Theorem 1.1
is exported, and Theorem 1.9 retains the paper's Hermite mechanism.

There is no standalone general diffusion theorem deriving Poincaré, LSI and
semigroup gradient bounds from `Γ₂ ≥ ρΓ`. Nor does the Gaussian solver export
the arbitrary-weight Hörmander theorem. These are limitations of general
infrastructure and original-proof coverage, not unproved completion inputs of
the concrete endpoints. The Bakry–Émery discussion below details the radial
inequalities and their proved ingredients.

Problems 1.11, 1.15 and 1.16 remain open research questions, and Appendix C
numerical experiments are uncertified. They are not established theorems with
missing Lean proofs. The combined independent follow-up review now resolves the identified concrete
items on their stated domains. Compilation and the Theorem 1.1 Palomar comparison
are separate evidence and do not replace this statement review. This table summarizes the
documented differences, rather than an exhaustive audit of every paper argument.

These remarks compare the proof bodies of the named endpoints with
[arXiv:2608.19358v2](https://arxiv.org/html/2608.19358v2). They supplement the
statement inventory above: an axiom audit does not establish that a proof follows
the paper. Each entry identifies a verified difference or explains why an apparent
difference is only additional infrastructure or a domain extension. This is a
review of the named routes, not a line-by-line fidelity certification of every
helper in the library. Future changes of route must receive a corresponding
remark under the working rule in [AGENTS.md](AGENTS.md).

### Theorem 1.1: the original analytic route is also exported

The weak Poincaré endpoint is supported by Hermite/coefficient estimates and
closure arguments. It is not the only realization of the main proof:
[FullMainAnalyticProof](GinibrePoincare/Endgame/FullMainAnalyticProof.lean)
also assembles the [original Section 2 route](https://arxiv.org/html/2608.19358v2#S2),
using the proved Vandermonde energy identity, actual entire-space Gaussian
distance estimate, divisibility and holomorphic–antiholomorphic projection
geometry. The original route's concrete inputs are theorems, not assumptions.
The separate Section 3 and Section 4 weak-domain endpoints are now proved in
[AlternativeSpectralPoincare](GinibrePoincare/Analysis/AlternativeSpectralPoincare.lean)
and [AlternativeSlaterPoincare](GinibrePoincare/Analysis/AlternativeSlaterPoincare.lean).
The spectral proof assembles the two normalized Vandermonde number forms,
the Gaussian number gap and the holomorphic–antiholomorphic projection bound;
it also exports the gap of the actual complex generator graph. The Hermite–Slater
proof uses actual normalized determinant representatives, their expansion,
Parseval and degree energy. Lean indexes all ordered orbital tuples, proving
that each distinct orbit has size n! and dividing the frame mass by n!;
this is equivalent to the paper's basis indexed by unordered orbital sets.
[AlternativeSlaterOrbits](GinibrePoincare/Analysis/AlternativeSlaterOrbits.lean)
proves the corresponding signed inner products, orthogonality and repeated-label
vanishing. [AlternativeSlaterLowering](GinibrePoincare/Analysis/AlternativeSlaterLowering.lean)
and [AlternativeSlaterPolynomial](GinibrePoincare/Analysis/AlternativeSlaterPolynomial.lean)
prove the actual Wirtinger lowering and holomorphic Vandermonde quotient.
[AlternativeSlaterEigenfunctions](GinibrePoincare/Analysis/AlternativeSlaterEigenfunctions.lean)
exports the pointwise determinant number-operator equation (4.2) and a literal
symmetric homogeneous polynomial quotient of degree `∑ aᵢ − n(n−1)/2`, as in
(4.6), with nonvanishing and degree bounds proved internally.
Both inequalities extend to the full symmetric ordinary weak-H¹ domain using
the internally proved weak-domain bridges. This extension is additional domain
coverage. [AlternativeSpectralDifferentialFactorization](GinibrePoincare/Analysis/AlternativeSpectralDifferentialFactorization.lean)
separately proves the literal complex pregenerator factorization and the two
Vandermonde differential expansions on smooth collision-free points.
[AlternativeSpectralSupport](GinibrePoincare/Analysis/AlternativeSpectralSupport.lean)
proves the full complex generator's spectrum is contained in `{0} ∪ (−∞,−2]`,
using the project's actual bounded two-sided graph-resolvent definition. Thus
`−Aₙ` has spectrum contained in `{0} ∪ [2,∞)`, as required by the paper. Lean expands the spectral-theorem
step by applying continuous functional calculus to a positive polynomial of the
actual resolvent, then constructs the literal graph inverse at every excluded
real or nonreal parameter. This uses the new two-sided number-form gap and
calls no earlier sharp Poincaré endpoint. The original Section 2 route remains
exported.

### Theorem 1.2: homogeneous-measure scaling for the Gamma radius

The equilibrium independence proof retains the paper's orthogonal decomposition
and Vandermonde translation invariance. For the Gamma radius law, the
[paper](https://arxiv.org/html/2608.19358v2#S1.SS6) uses polar coordinates on the
recentered hyperplane. [GinibreRadialGamma](GinibrePoincare/Analysis/GinibreRadialGamma.lean)
instead determines the radial pushforward by sublevel-set scaling of a
homogeneous weighted measure, using
[HomogeneousRadialMeasure](GinibrePoincare/Analysis/HomogeneousRadialMeasure.lean).
Gaussian tilting and probability normalization then give the Gamma density.
The homogeneity principle is the same, but the measure calculation avoids an
explicit polar-coordinate change of variables.

### Theorem 1.3: Brownian drivers and their independence

The projected SDE identities and Itô calculation of the CIR equations follow
the [paper's factorization proof](https://arxiv.org/html/2608.19358v2#S1.SS6).
For the radial drivers, the paper uses joint quadratic variation and Lévy
characterization. Lean constructs stochastic integrals of adapted unit fields
and proves their Gaussian increment laws through discrete Brownian sums and
limits in
[GinibreStochasticUnitFieldBrownian](GinibrePoincare/Analysis/GinibreStochasticUnitFieldBrownian.lean).
It then proves independence through measurable Lamperti functionals of the
independent center and relative paths in
[GinibreStochasticRadialCenterIndependence](GinibrePoincare/Analysis/GinibreStochasticRadialCenterIndependence.lean)
and [GinibreStochasticCenterRadialDriverIndependence](GinibrePoincare/Analysis/GinibreStochasticCenterRadialDriverIndependence.lean).
This replaces the joint Lévy-characterization step; zero initial center and
zero-speed cases are additional coverage, not alternative CIR formulas.

### Corollary 1.5: a direct center-power proof

The [paper's corollary](https://arxiv.org/html/2608.19358v2#S1.SS7) follows the
Hermite–Laguerre polynomial eigenfunctions of Theorem 1.4 and their inclusion in
the generator domain. The all-positive-n Lean endpoint instead proves that
the coordinate-sum powers `S^k` belong to the actual full generator domain and
are nonzero eigenvectors. See
[GinibreOneParticleSpectrum](GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean).
These powers are already members of the paper's family for n ≥ 2; the direct
proof avoids the relative-radius sector and also handles n = 1. Theorem 1.4's
Hermite–Laguerre construction remains separately formalized. The normalization
and spectral points are unchanged; including n = 1 is a domain clarification.

### Lemma 1.7: an explicit collapsing configuration

The [paper's proof](https://arxiv.org/html/2608.19358v2#S1.SS8) isolates one
colliding pair, keeps the other separations bounded away from zero, and uses a
tangential relative direction. The endpoint in
[GinibrePointwiseCurvature](GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean)
instead places all particles at distinct real coordinates `i/L` and lets L grow.
An imaginary coordinate direction has squared norm one; every relevant
interaction contribution is nonpositive, so one pair suffices to bound the
Hessian above by a quantity tending to minus infinity. This is a different
witness construction for the same curvature obstruction. The separately proved
recentered obstruction in
[GinibrePointwiseCurvatureTangent](GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean)
uses an actual center-zero direction.

### Theorems 1.9 and 1.10: Hermite identity versus differential derivation

For Theorem 1.9, the Hermite levels, projection geometry and algebraic passage
to the second deficit follow the mechanism in
[paper Section 6](https://arxiv.org/html/2608.19358v2#S6).
[FullTheoremOneNine](GinibrePoincare/Endgame/FullTheoremOneNine.lean)
extends the result to the actual real symmetric generator graph, with a separate
weak-H¹ first-deficit endpoint. Those closure results are domain extensions,
not an alternative proof of the smooth-core identity.

The previously exported Theorem 1.10 endpoint uses a different route. The paper develops the
differential expression through the integrated Bochner–Kodaira identity and
the number operator. In
[FullTheoremOneTen](GinibrePoincare/Endgame/FullTheoremOneTen.lean), Lean starts
from the already proved Theorem 1.9, constructs the inverse square root through
Hermite coefficients, proves that the synthesized first and second derivatives
are actual weak derivatives, and identifies their summed squared norms with the
Hermite tail. Rewriting the Hermite deficit then gives the differential formula.
Thus this endpoint is not an independent implementation of the paper's
Bochner–Kodaira proof, even though concrete Bochner identities are proved
elsewhere. The ordinary Schwartz derivative endpoint and generator-domain
extension are additional domain bridges, not substitutes for the differential
statement.

The independent [BochnerKodairaTheoremOneTen](GinibrePoincare/Endgame/BochnerKodairaTheoremOneTen.lean)
now gives both deficits on the same actual generator graph, with coefficients
4/n and 8/n and ordinary Schwartz distributional derivatives. Its proof uses
[AlternativeBochnerKodairaDifferential](GinibrePoincare/Analysis/AlternativeBochnerKodairaDifferential.lean)
for the literal commutator and
[AlternativeBochnerKodairaIntegration](GinibrePoincare/Analysis/AlternativeBochnerKodairaIntegration.lean)
for integration by parts with vanishing radial cutoff boundaries.
[Identity](GinibrePoincare/Analysis/AlternativeBochnerKodairaIdentity.lean)
and [Polynomial](GinibrePoincare/Analysis/AlternativeBochnerKodairaPolynomial.lean)
prove the integrated identity on actual finite Hermite polynomials;
[AlternativeSpectralNumberPolynomial](GinibrePoincare/Analysis/AlternativeSpectralNumberPolynomial.lean)
identifies their literal number operator with its multiplier.
[InverseRoot](GinibrePoincare/Analysis/AlternativeBochnerKodairaInverseRoot.lean)
then closes the identity through actual bounded derivative-synthesis limits.
The second deficit follows from generator integration by parts and elementary
norm algebra in [GinibreGeneratorDeficitAlgebra](GinibrePoincare/Analysis/GinibreGeneratorDeficitAlgebra.lean).
This expands the paper's spectral calculus and closure step using explicit
polynomial approximation; it does not assert equality of the compact-jet
closure with every number-operator domain. Compiled dependency checks on the
transitive proof bodies confirm that the new endpoint does not invoke the
old Theorem 1.9/1.10 deficits or Hermite second-energy identities. The existing
Hermite-derived endpoint remains exported.

### Theorems 1.12 and 1.13: expanding the Gaussian LSI ingredient

The quadratic radial reduction follows the
[paper's Kostlan/Gaussian magnitude lift](https://arxiv.org/html/2608.19358v2#S7);
it should not be described as replacing that proof by a different radial
argument. The Gaussian LSI used there and in the matrix lift is itself proved
internally, whereas the paper uses it as a standard ingredient.
[GaussianLSIReal](GinibrePoincare/Analysis/GaussianLSIReal.lean) derives the
one-dimensional inequality from the finite Bernoulli-cube LSI, a binomial
central-limit passage, and Sobolev closure. Scaling and entropy tensorization
then give the Gaussian product inequalities. This is an expanded proof of a
cited ingredient; it is not a Bakry–Émery derivation of that ingredient.
The matrix spectral pushforward and overlap-gradient calculations remain
separate obligations; Gaussian LSI alone does not supply them.

### Theorem 1.13: the Gaussian matrix Poincaré route is also implemented

The [paper's matrix proof](https://arxiv.org/html/2608.19358v2#S1.SS9)
applies Gaussian matrix Poincaré to the spectral lift. This route now has its own
concrete endpoint `matrixSpectralLift_finite_overlap_gaussian_poincare` in
[AlternativeMatrixPoincare](GinibrePoincare/Analysis/AlternativeMatrixPoincare.lean).
The actual matrix Gaussian inequality is proved on the compact C¹ core by
linearizing the internally proved Gaussian LSI, including two differentiations
under the actual probability integral, and then extended to the actual matrix
H¹ closure. This expands a standard Gaussian ingredient cited by the paper.
Spectral pushforward identifies the variance; the literal matrix gradient energy
is four times the overlap energy. Ordinary weak derivatives across collision
matrices and membership in the actual H¹ completion are derived internally from
finite overlap energy. No Ginibre Poincaré theorem or overlap lower-bound
comparison is invoked. `fullMatrixLift_functional_inequalities` now uses this
Gaussian route for the variance bound; the entropy proof remains Gaussian LSI
transfer. Focused and full compilation, public/private standard-axiom audits and
compiled transitive proof-body independence checks pass for both matrix bounds.

The previous proof in
[MatrixSpectralLiftPoincareFinite](GinibrePoincare/Analysis/MatrixSpectralLiftPoincareFinite.lean)
remains available: it uses Theorem 1.1 plus ordinary-gradient/overlap domination.
Both proofs obtain coefficient `2/n`; their arguments are recorded separately.

### Gaussian dbar estimates and Appendix B: explicit spectral foundations

The coefficient proof of Lemma 2.2 uses the paper's Hermite/Parseval mechanism.
Its foundational completeness input is developed explicitly through Gaussian
moment/Fourier tests and uniqueness in
[GaussianPolynomialCompleteness](GinibrePoincare/Analysis/GaussianPolynomialCompleteness.lean)
and [GaussianFourierUniqueness](GinibrePoincare/Analysis/GaussianFourierUniqueness.lean).
This expands a standard basis ingredient used by the paper; it does not change
the deficit argument. Rodrigues and lowering identities remain separately proved.

For Remark 2.4, the paper invokes the Hörmander–Berndtsson solvability theorem.
Lean provides an explicit Gaussian spectral solver: distributional closedness
implies compatibility of Hermite coefficients, from which it constructs a
potential and proves the actual derivative equations. See
[GaussianClosedFormVolume](GinibrePoincare/Analysis/GaussianClosedFormVolume.lean)
and [GaussianClosedFormCurl](GinibrePoincare/Analysis/GaussianClosedFormCurl.lean).
[GaussianCanonicalDbarSolution](GinibrePoincare/Analysis/GaussianCanonicalDbarSolution.lean)
then projects off the entire kernel to obtain the canonical minimum-norm
solution. This is a Gaussian-specific construction, not an export of the
arbitrary-weight Hörmander theorem.

For Remark 2.3's compact-core density, the paper describes cutoff and
mollification. [GaussianDbarCompactCore](GinibrePoincare/Analysis/GaussianDbarCompactCore.lean)
uses finite Hermite graph approximation followed by spatial cutoffs instead.
For Remark 2.5, Lean additionally identifies the actual entire L² space with
the closed zero-mode span and reconstructs representatives in
[GaussianEntireSpaceClosure](GinibrePoincare/Analysis/GaussianEntireSpaceClosure.lean).
The paper's local bounds and locally uniform convergence are also exported;
the spectral characterization is additional infrastructure.

### Lemma 2.6: integral division rather than holomorphic local algebra

The [paper's divisibility proof](https://arxiv.org/html/2608.19358v2#S2.SS3)
uses local Weierstrass division and factorization in holomorphic germs.
[GaussianEntireHyperplaneDivision](GinibrePoincare/Analysis/GaussianEntireHyperplaneDivision.lean)
instead constructs division by a linear hyperplane through an explicit interval
integral of a directional derivative.
[EntireVandermondeFactorization](GinibrePoincare/Analysis/EntireVandermondeFactorization.lean)
then divides successively by the finite collision factors, preserving vanishing
on the remaining hyperplanes. The quotient is proved entire and symmetric
across collisions; restricting it to the collision-free set would not prove
the paper's statement.

### Theorem 1.4, Remark 1.6 and Appendix A: same mechanisms, domain bridges

The Hermite–Laguerre chain-rule proof and the relative-phase quadratic witness
follow the paper in
[PolynomialEigenfunctionGenerator](GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean)
and [PolynomialSectorIncompleteness](GinibrePoincare/Analysis/PolynomialSectorIncompleteness.lean).
They are not listed as alternative proofs. Appendix A's core and collision
arguments likewise acquire additional explicit weak-graph identifications:
[GinibreRealCoreClosureEquivalence](GinibrePoincare/Analysis/GinibreRealCoreClosureEquivalence.lean)
proves equality with an independently defined ordinary distributional graph.
This is a stronger domain characterization, rather than evidence that the
paper's approximation mechanism has been replaced.

### Generator and semigroup: a resolvent implementation

The [paper's dynamics discussion](https://arxiv.org/html/2608.19358v2#S1.SS5)
uses the closed Dirichlet form, Friedrichs extension and general diffusion
correspondence. Lean realizes the same weak form using a Hilbert-space Riesz
resolvent in
[GinibreFullGeneratorResolvent](GinibrePoincare/Analysis/GinibreFullGeneratorResolvent.lean)
and builds the analytic semigroup by bounded continuous functional calculus of
that resolvent in
[GinibreFullSemigroup](GinibrePoincare/Analysis/GinibreFullSemigroup.lean).
The original-SDE transition semigroup is identified through its actual Laplace
resolvent and semigroup uniqueness in
[GinibreTransitionAnalyticResolventSemigroupComparison](GinibrePoincare/Analysis/GinibreTransitionAnalyticResolventSemigroupComparison.lean).
This is a concrete implementation of the operator construction with a different
semigroup-identification argument, rather than an invocation of the paper's
general Hunt-process correspondence. The weak-form and paper-speed
identifications are proved separately.

### Theorem 1.14: primary Euclidean lift and independent transport proof

The [versioned paper's proof and footnote 6](https://arxiv.org/html/2608.19358v2#S1.SS10)
apply the strongly convex Bakry–Émery LSI to a Euclidean lift of each radius
law, then use the norm map, tensorization and Kostlan gradient transfer. This
primary route is now formalized by
[AlternativeBakryEmeryPotentialRadialLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLSI.lean),
and the nonquadratic endgame invokes it. The independent transport proof
permitted by footnote 6 remains exported in `StrongConvexPotentialRadialLSI`.

Lean expands the cited strongly convex Gibbs ingredient: an actual Gaussian
Faber–Schauder series constructs independent continuous Brownian coordinates;
the global strongly convex Langevin flow has a proved Cameron–Martin response;
finite Gaussian noise-grid inequalities pass to the Brownian law and Gibbs
stationary limit. Stopped Girsanov identities, OU reference reversal and
compact-ball exhaustion prove Gibbs invariance internally.
[ConvexGibbsLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryConvexGibbsLSI.lean)
therefore exports actual normalized Gibbs LSI with coefficient `2/κ`, without
stochastic or analytic completion inputs. This is an expanded proof of the
paper's cited ingredient, not a parabolic `Γ₂` entropy-interpolation proof or
a standalone arbitrary-diffusion curvature theorem.

The smooth positive regularization has exact curvature `κ = nρ`.
[LiftLSILimit](GinibrePoincare/Analysis/AlternativeBakryEmeryLiftLSILimit.lean)
passes entropy and actual gradient expectations to the unregularized density
under proved Gaussian domination. Actual Haar absolute continuity, spatial
cutoffs and mollification extend the inequality to bounded Lipschitz functions.
[RadiusLaw](GinibrePoincare/Analysis/AlternativeBakryEmeryRadiusLaw.lean)
identifies the normalized lift's norm law and its almost-everywhere gradient
energy exactly. Finite-product entropy tensorization and the actual Kostlan
transfer finish the paper's smooth compact radial inequality with coefficient
`2/(nρ)`, and a bounded Lipschitz radial domain extension. This extension does
not claim an arbitrary unbounded weak-Sobolev LSI domain for nonquadratic laws.
The generic scalar entropy-flow and factor-assembly lemmas remain explicitly
labeled reductions; every input used by the concrete endpoint is discharged.

The Poincaré part develops the same weighted-dbar coercivity/duality mechanism
in a concrete Hilbert-space realization:
[NonQuadraticDbarL2](GinibrePoincare/Analysis/NonQuadraticDbarL2.lean) derives
weak solvability from the proved adjoint bound, and
[GeneralPotentialSharpPoincare](GinibrePoincare/Analysis/GeneralPotentialSharpPoincare.lean)
combines the quotient gap with centered projection/phase geometry. This expands
the paper's Hörmander–Berndtsson input and represents its holomorphic geometry
through actual closed spaces; the analytic bound is proved internally.

## Bakry–Émery and the radial log-Sobolev proofs

The full configuration law and the radial laws have different curvature
properties. For Ginibre with n ≥ 2, the normalized configuration Hessian is
unbounded below, including on relative directions. This is proved by
`ginibre_pointwise_bakry_emery_curvature_unbounded_below` in
[GinibrePointwiseCurvature](GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean)
and its recentered counterpart. The standard positive pointwise
Bakry–Émery bound therefore cannot be applied directly to the full Ginibre
configuration diffusion. The full real symmetric generator nevertheless
satisfies the integrated curvature inequality `2 * energy ≤ ‖Lf‖²`, proved
by `ginibreFullGenerator_integrated_curvature` in
[GinibreFullSemigroupDeficitConsequences](GinibrePoincare/Analysis/GinibreFullSemigroupDeficitConsequences.lean).

After Kostlan reduction, the independent positive-radius laws have densities
proportional to `r^(2k−1) exp(−nQ(r))`, with paper indexing k = 1, …, n.
For a rotational ρ-convex potential V(z) = Q(|z|), their effective potentials obey

$$
W_k(r)=nQ(r)-(2k-1)\log r,\qquad
W_k''(r)=nQ''(r)+\frac{2k-1}{r^2}\ge n\rho
\quad (r>0).
$$

The exact derivative and radial curvature bound are formalized as
`radialEffectivePotential_second_derivative` and
`rhoConvexPotential_radial_curvature` in
[NonQuadraticRadialConfinement](GinibrePoincare/Analysis/NonQuadraticRadialConfinement.lean).
Positive radial curvature is compatible with the negative configuration
curvature above: these are different measures and operators.

The [versioned paper's Theorem 1.14 proof and footnote 6](https://arxiv.org/html/2608.19358v2#S1.SS10)
use a strongly convex Euclidean lift of each radius law to invoke Bakry–Émery,
and explicitly allow contraction/transport arguments as alternatives. The
quadratic Lean endpoint follows the Gaussian-lift route, while the
nonquadratic endpoint now uses the primary Euclidean-lift route as well:

- **Quadratic Ginibre, Theorem 1.12:** `radial_core_lsi` and
  `radial_sobolev_lsi` in
  [FullRadialLSIReduction](GinibrePoincare/Analysis/FullRadialLSIReduction.lean)
  transfer the proved Gaussian block LSI through the radial lift and complete
  the weak-domain approximation.
- **Nonquadratic radial extension, Theorem 1.14:**
  `bakryEmery_kostlan_radius_bounded_lsi` in
  [AlternativeBakryEmeryRadialLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryRadialLSI.lean)
  follows from the actual strongly convex Euclidean Gibbs lift.
  [AlternativeBakryEmeryRadialProductLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryRadialProductLSI.lean)
  proves the product inequality, and `bakryEmery_potential_smooth_radial_lsi` in
  [AlternativeBakryEmeryPotentialRadialLSI](GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLSI.lean)
  transfers it to the interacting law, with the paper coefficient `2/(nρ)`
  multiplying the ordinary Euclidean gradient energy. The previously verified
  `rhoConvex_*` Gaussian quantile proof remains a separate implementation.

Thus the radial LSI endpoints do not assume an unproved Bakry–Émery criterion.
The library also proves concrete scalar/radial Bochner, coercivity and Fisher
curvature estimates. It does not export a standalone general diffusion theorem
that derives Poincaré, LSI and semigroup gradient bounds from `Γ₂ ≥ ρΓ`.
This limitation concerns reusable general infrastructure, not a missing analytic
hypothesis in the proved radial LSI statements. The four requested proof groups have independent endpoints; this does not
claim an exhaustive formal correspondence for every argument in the paper.

## Scope qualifications

Theorems 1.9 and 1.10 use the actual real symmetric generator graph. The differential theorem now also has a literal ordinary Schwartz distributional endpoint, proved equivalent to the independent weighted compact-test graph. Sharp equality is
classified on the full symmetric weak domain. Matrix inequalities include the actual Gaussian matrix H¹ hypothesis; the
ordinary spectral derivative and finite overlap energy are derived internally. Nonquadratic inequalities use the stated
potential hypotheses and smooth compact symmetric observables, with a radial
restriction for log-Sobolev. Joint two-radius CIR realization is for n ≥ 2 and
deterministic collision-free initial configurations. Stochastic invariance and
analytic semigroup identification cover n > 0 and every nonnegative speed and
horizon.

The numbered inventory records statement correspondence; the axiom audits separately verify compilation and permitted axiom usage. They are not an independent mathematical peer review of every definition or proof.

## Build, audit and source evidence

The current full-tree evidence and refreshed physical Lean line counts are
recorded in [STATUS.md](STATUS.md) and [verification/correspondence-final-check.txt](verification/correspondence-final-check.txt).
The public and all-local audits cover completion exports and private helpers;
the authorized independent Challenge statement hole is excluded from the
proof-library/Solution closure. Only the three permitted standard axioms may
occur. The final compiled declaration export supplies the regenerated endpoint
graphics and interactive dependency explorer.

Source counts are generated by `python3 scripts/count_lean_sources.py`, include
comments and blank lines, and count each transitively imported Mathlib module
once in full. Archives, Lean core and other dependencies are excluded.

The earlier supported-toolchain Comparator checkpoint compares full symmetric
weak-H¹ Theorem 1.1 and exhaustive affine equality only. It passed strict
recursive statement comparison and all three kernels. This proof-library
update does not assert a new full-paper Comparator review or a public registry
registration receipt.

## Final assembly and repository state

The original analytic main proof, both Hermite deficits and both differential deficits are exported and audited. Generator membership and actual derivative-domain theorems supply the analytic facts required by those formal statements; none remains a completion assumption. The literal integrated pointwise Γ₂ bridge and the itemized review gaps are now closed by the correspondence endpoints, with affirmative independent follow-up findings on their precise domains. Corollary 1.5 covers every positive dimension and positive speed. Appendix A.2 includes actual graph-norm comparison and real/complex global versus collision-free core equality.

The user-authorized fresh Git snapshot includes the final proofs, thematic subprojects, reports, pinned dependency manifest and verification logs. The project is published at [djalilchafai/ginibre-poincare](https://github.com/djalilchafai/ginibre-poincare), and Palomar intake and official mechanical verification have completed. Later documentation commits do not change the submitted snapshot. No additional Mathlib checkout was created. The final v4.35.0-rc2 build and audits above supersede earlier checkpoints preserved in STATUS.md.

## Proof routes for the correspondence-completion additions

| Result | Versioned paper route | Lean route and modules |
| --- | --- | --- |
| Literal Theorem 1.9 Γ₂ deficit and (1.42) | Integrated carré-du-champ identity and Hermite sum of squares | The same Hermite mechanism plus unrestricted ordinary Green identities proves the literal integral in `CorrespondenceOperatorUnrestrictedGamma` and `FullTheoremOneNinePointwiseGamma`. `CorrespondenceCurvatureCriterion` states the specific PI/Γ₂ equivalence by independently proving both concrete assertions; no universal external equivalence theorem is claimed. |
| Theorem 1.13 matrix H¹ domain | Gaussian matrix Sobolev inequality and local spectral differentiation | `CorrespondenceMatrixWeakClosure` expands the Sobolev/local derivative bridge, using simple-spectrum openness and a.e. simple spectrum. Derivative identification and overlap integrability are conclusions. The Gaussian proof route is also formalized. |
| Section 6 maximal N, compact core, (6.9), spectrum and roots | Gaussian differential number operator, Bochner–Kodaira identity, operator closure and spectral calculus | `CorrespondenceOperatorNumber*` uses the complete Hermite basis for the maximal graph and actual Mathlib resolvent CFC for the roots. The paper's compact C∞ graph core and full-domain ordinary first/second-derivative Bochner–Kodaira identity are also proved. Weak-domain transfer in `NumberTransfer` is a domain extension. |
| Unrestricted diffusion and square-root domain | Closed Dirichlet form, Friedrichs/Hunt construction and cited martingale/SDE correspondence | `CorrespondenceOperator*` proves the concrete unrestricted form, actual self-adjoint generator and square-root H¹ domain. `CorrespondenceDynamics*` constructs continuous strong Markov paths directly from the original Brownian diffusion, then identifies the martingale problem and actual analytic semigroup. This is an alternative concrete construction, not a universal external correspondence theorem. |
| Unstopped independent CIR equations | Quadratic variation and Lévy characterization | `CorrespondenceDynamicsGlobalCIR` extends the internally proved discrete Brownian-sum integrals through actual localization limits. Independence follows measurable functionals of independent paths; the global equations now match the paper. |
| Real GUE contextual PI/LSI | Strong convexity on the ordered chamber and standard convex-measure inequalities | `CorrespondenceGUE*` expands this cited ingredient using explicit log-barrier regularization, actual normalized chamber/full measures and limits. Exact 1/n and 2/n constants and optimal witnesses hold on the paper's smooth compact H¹ completion; the C¹ finite-energy endpoint is an extension. |
| General real Brascamp–Lieb contextual assertion | Citation to Brascamp–Lieb (1976), Th. 4.1; no displayed hypotheses in this paper | `CorrespondenceBrascampLieb*` proves the classical Hessian-inverse conclusion, with the precise C²/positive-Hessian/locally-Lipschitz hypotheses documented by the primary [Carlen–Cordero-Erausquin–Lieb (2013) statement](https://www.numdam.org/item/AIHPB_2013__49_1_1_0/). `CorrespondenceWeightedElliptic*` proves local regularity, cutoff energy and Liouville internally; dense range and duality close the inequality. Ordinary local weak derivatives give an additional domain extension. Exact fidelity to the inaccessible 1976 proof is not claimed. |
| Remark 2.5 arbitrary-weight entire closedness and local uniform convergence | Mean-value bounds on compact sets | `CorrespondenceAuxiliaryPositiveWeight*` proves distributional CR reconstruction and joint Weyl regularity, then actual compact mean-value bounds and locally uniform convergence. Closedness uses an alternative distributional route; the paper's local uniform conclusion is also proved. |
| Remark 2.4 footnote 7 local Dolbeault lemma | Cited local ∂bar exactness | `CorrespondenceAuxiliaryLocalDolbeault*` and `CorrespondenceDolbeaultYoung*` expand the ingredient through actual Cauchy–Green kernels, bounded ordinary L² finite homotopy and genuine mollification/strong limits. Arbitrary open sets and all dimensions are covered; locally L² coefficients extend the smooth source domain. |
| Δlog|z|=2πδ₀ | Classical planar fundamental solution | `CorrespondenceLog*` expands the distributional calculation via actual regularized kernels, ordinary compact tests and dominated limits, with the exact 2π normalization. |
| Appendix A cutoff rates | Pair-tube bounds and product cutoffs | `CorrespondenceCollision*` follows this route with explicit density cancellation, O(ε⁴) squared-value error and O(ε²) gradient energy, plus actual collision-free support. |
| Appendix B triangular expansion and Gram–Schmidt | Repeated Gaussian integration by parts and triangularity | `CorrespondenceAuxiliaryHermiteLeading`, `TensorExpansion` and `TensorGramSchmidt` use the explicit tensor expansion, proved orthonormality and uniqueness of ordinary normalized Gram–Schmidt. Completeness retains the expanded Fourier-uniqueness polynomial-density proof; exact repeated-IBP proof fidelity is not claimed. |

These result-specific remarks distinguish alternative constructions, expanded
proofs of cited ingredients and domain extensions. The independent reviews
check statement correspondence, not literal reproduction of every proof line.
