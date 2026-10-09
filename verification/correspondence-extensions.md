# Independent correspondence review: factorization, deficits and extensions

> Revision context (2026-10-09): this document preserves its original dated
> mathematical source-review findings and snapshots. The later readability
> revision has a separate [semantic diff review](readability-semantic-review.md)
> and [build/axiom verification record](readability-final-check.txt); it is not a
> new review against the paper. See [STATUS](../STATUS.md) for current evidence.

> Historical review at proof snapshot `0779d080f22fcd93258f0e6e0cb34944bada110c`. Its findings are retained as evidence, not current unresolved-work labels. See the [current extension follow-up](correspondence-extensions-followup.md) and [integrated review](../CORRESPONDENCE_REVIEW.md) for item-specific resolutions and remaining qualifications.

Reviewed on 2026-10-08 by the independently assigned `review_extensions`
agent against source snapshot `0779d080f22fcd93258f0e6e0cb34944bada110c`.
The authority is [arXiv:2608.19358v2](https://arxiv.org/html/2608.19358v2),
downloaded directly; local TeX was not used. Lean source was read without
changing it. This is a correspondence review, not another kernel audit.

This review enumerates the assertions in Sections 1.6–1.10 and calculations
in Sections 5–7. Section 1.6's Theorem 1.3 stochastic assertions are delegated
to the separate dynamics review. Historical/contextual statements and cited
results about other models are not certificates of this paper's endpoints.
“Verified” below means the inspected statement and definitions match the
specified assertion. “Related” means proved infrastructure is present but
the literal correspondence bridge was not located or independently checked.
An item marked related must not be promoted to a full-paper correspondence
pass. Module links use source line numbers at the reviewed snapshot.

## Findings requiring qualification

1. **Theorem 1.13's literal H¹ hypothesis remains related.**
   [AlternativeMatrixPoincare.lean:28](../GinibrePoincare/Analysis/AlternativeMatrixPoincare.lean#L28)
   proves the H¹ variance result with two further arguments: a value
   representative equality `hv` and derivative equalities `hd`.
   [MatrixSpectralLiftLSITransport.lean:68](../GinibrePoincare/Analysis/MatrixSpectralLiftLSITransport.lean#L68)
   has the same requirement for entropy. The value equality is ordinary H¹
   membership data; `hd` identifies the closed derivative with the classical
   derivative on the simple-spectrum set. A theorem deriving `hd` from
   membership alone was not found. The fully assembled finite-overlap
   endpoint is concrete and its coefficient is correct, but has different
   hypotheses. Its construction of H¹ membership does not prove the reverse
   implication needed to identify the literal paper domain.
2. **Equation (1.39), the integral of pointwise Γ₂, remains related.**
   The actual pointwise formula is proved in
   [GinibrePointwiseBochner.lean:94](../GinibrePoincare/Analysis/GinibrePointwiseBochner.lean#L94).
   The deficit endpoints use `‖A f‖²`. Repository searches found no theorem
   identifying the integral of `ginibrePointwiseGammaTwo` with this squared
   norm. This does not invalidate either asserted deficit identity, whose
   paper statement already uses `‖A f‖²`, but leaves this separate displayed
   calculation without an identified endpoint.
3. **The three degree-two examples in (1.35) remain related.**
   [PolynomialEigenfunctions.lean:118](../GinibrePoincare/Analysis/PolynomialEigenfunctions.lean#L118)
   defines `P_200`, `P_110`, `P_020` by the displayed formulas. Only the first
   four examples have equality lemmas connecting these names to the actual
   family `polynomialEigenfunction`. No such equality lemma was found for
   these three degree-two indices. Definitions of the desired answers do
   not independently certify those identifications.
4. **The symmetric-polynomial counterexample before Theorem 1.4 remains
   related.** The paper computes the generator of `Σ z_j²` and says its
   image is not a polynomial. No identified endpoint proves this exact
   calculation and non-polynomial conclusion. The sector incompleteness
   theorem proves a different claim.
5. **The full operator-core/spectral-calculus paragraph in Section 6 remains
   related as a literal proof correspondence.** The independent
   Bochner–Kodaira route has genuine compact differential identities,
   closed-jet identities, and finite-polynomial approximation of the
   particular inverse-root vector. It reaches the exact theorem without
   assuming analytic completion facts. A theorem identifying the compact
   jet closure with the entire operator domain of the paper's unbounded
   number operator, together with its literal spectrum statement, was not
   identified in this review. Its particular-vector closure route should
   be distinguished from that general operator-core assertion.

No numerical coefficient mismatch was found in the inspected final
inequalities or deficits. These findings prevent an exhaustive affirmative
full-paper correspondence verdict at this snapshot.

## Numbered statements and their immediate claims

| Paper anchor / assertion | Status | Inspected Lean evidence and qualification |
| --- | --- | --- |
| [Theorem 1.2, (1.25)](https://arxiv.org/html/2608.19358v2#S1.SS6): center/relative decomposition and density splitting | Verified | `decomposition_eq`, `pythagorean_identity`, `vandermonde_translation_invariant`, `normalized_equilibrium_factorization` in [EquilibriumFactorization.lean:44](../GinibrePoincare/Analysis/EquilibriumFactorization.lean#L44), lines 165, 203, 282. Particle number is positive. |
| Theorem 1.2: standard complex Gaussian coordinate sum, independence and intrinsic relative density | Verified | `coordinateSum_ginibre_gaussian`, `equilibrium_jointLaw`, `recenteredGinibreMeasure_eq_withDensity`, `coordinateSum_recentered_indepFun` in [EquilibriumProbability.lean:197](../GinibrePoincare/Analysis/EquilibriumProbability.lean#L197), lines 218, 233, 259. Intrinsic Haar normalization cancels in the normalized relative density. |
| Theorem 1.2: Gamma radius and its shape | Verified | `radialObservable_ginibre_gamma`, `recenteredGammaShape_eq` in [GinibreRadialGamma.lean:278](../GinibrePoincare/Analysis/GinibreRadialGamma.lean#L278), line 71. Shape is `(n−1)(n+2)/2`, rate 1, and Gamma statement requires `n≥2`. |
| Theorem 1.2: one-particle degeneracy | Verified | `recentered_one`, `radialObservable_one` in [EquilibriumFactorization.lean:291](../GinibrePoincare/Analysis/EquilibriumFactorization.lean#L291); the Gaussian sum law above includes `n=1`. |
| [Theorem 1.4, (1.31)–(1.33)](https://arxiv.org/html/2608.19358v2#S1.SS7): definitions, symmetry and differential eigenvalue | Verified | `R_poly_eq`, `polynomialEigenfunction`, `polynomialEigenfunction_permute` in [PolynomialEigenfunctions.lean:30](../GinibrePoincare/Analysis/PolynomialEigenfunctions.lean#L30), lines 58, 95; `polynomialEigenfunction_eigenvalue_equation_atSpeed` in [PolynomialEigenfunctionGenerator.lean:95](../GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean#L95). Eigenvalue is `2α/n*(a+b+2m)`; the pointwise equation is on the collision-free set, `n≥2`. |
| Theorem 1.4: basis and invariant algebra | Verified | `polynomialEigenfunction_unique_finite_expansion` in [PolynomialEigenfunctionBasis.lean:87](../GinibrePoincare/Analysis/PolynomialEigenfunctionBasis.lean#L87) and `complexGinibrePregenerator_sumRadiusPolynomial` in [SumRadiusGenerator.lean:100](../GinibrePoincare/Analysis/SumRadiusGenerator.lean#L100). Actual finite expansions and differential action are proved. |
| Theorem 1.4: orthogonality, including equal-eigenvalue indices | Verified | `polynomialEigenfunction_equilibrium_orthogonal` in [PolynomialEquilibriumOrthogonality.lean:117](../GinibrePoincare/Analysis/PolynomialEquilibriumOrthogonality.lean#L117), with separate-index criterion and factorized inner product at line 97. Laguerre normalization is not falsely claimed orthonormal. |
| (1.34): first four examples | Verified | `polynomialEigenfunction_zero`, `polynomialEigenfunction_first_radial`, `polynomialEigenfunction_first_holomorphic`, `polynomialEigenfunction_first_antiholomorphic` in [PolynomialEigenfunctions.lean:124](../GinibrePoincare/Analysis/PolynomialEigenfunctions.lean#L124). |
| (1.35): next three examples | Related | Finding 3. |
| [Corollary 1.5, (1.36)](https://arxiv.org/html/2608.19358v2#S1.E36): spectral inclusion at positive speed | Verified | `ginibreFullGeneratorAtSpeed_all_positive_n_spectrum_containment` in [GinibreOneParticleSpectrum.lean:242](../GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean#L242). Actual closed symmetric generator graph; ordinary unbounded spectrum defined through bounded two-sided resolvents. Stronger than stated particle restriction: every `n>0`. |
| Corollary 1.5: eigenfunctions are in the full domain | Verified for spectral witnesses; related for exhaustive family bridge | `ginibreFullGenerator_coordinateSum_power_eigenpair` in [GinibreOneParticleSpectrum.lean:159](../GinibrePoincare/Analysis/GinibreOneParticleSpectrum.lean#L159) suffices for every claimed spectral point. Polynomial sector weak-core construction is present in [PolynomialGeneratorWeakCore.lean:66](../GinibrePoincare/Analysis/PolynomialGeneratorWeakCore.lean#L66); this review did not trace every family member through its full-generator bridge. |
| [Remark 1.6](https://arxiv.org/html/2608.19358v2#S1.SS7): excluded quadratic, nonzero and orthogonal | Verified | `ginibreCenteredQuadraticL2_ne_zero` and the concluding `polynomialSector_incomplete` in [PolynomialSectorIncompleteness.lean:92](../GinibrePoincare/Analysis/PolynomialSectorIncompleteness.lean#L92). Proof uses actual relative-phase invariance and quarter-turn, which suffices in place of arbitrary-angle cancellation. |
| Remark 1.6: arbitrary-angle covariance and decomposition `Σz_j²=S²/n+Q` | Related | The actual quadratic and quarter-turn proof were checked; literal arbitrary-angle formula and final decomposition were not located. |
| [Lemma 1.7](https://arxiv.org/html/2608.19358v2#S1.SS8): no lower curvature bound | Verified with paper's necessary `n≥2` qualification | `ginibre_pointwise_bakry_emery_curvature_unbounded_below` in [GinibrePointwiseCurvature.lean:90](../GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean#L90). Actual collision-free configurations and unit directions. The terse lemma omits `n≥2`; the surrounding paper explicitly treats `n=1` as Gaussian. |
| [Remark 1.8, (1.41)](https://arxiv.org/html/2608.19358v2#S1.E41): harmonic interaction and mean curvature 2 | Verified | `ginibre_pointwise_mean_curvature` in [GinibrePointwiseCurvature.lean:103](../GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean#L103), using actual Hamiltonian Laplacian. Denominator is `n*(2n)`. |
| Remark 1.8: relative curvature still unbounded below | Verified | `ginibre_recentered_pointwise_curvature_unbounded_below` in [GinibrePointwiseCurvatureTangent.lean:127](../GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean#L127). Constructed direction has zero coordinate sum and Euclidean norm one. |
| [Theorem 1.9, (1.44), (1.45)](https://arxiv.org/html/2608.19358v2#S1.SS8): both Hermite deficits | Verified | `fullTheoremOneNine` in [FullTheoremOneNine.lean:20](../GinibrePoincare/Endgame/FullTheoremOneNine.lean#L20). Generator-domain extension, positive-mode summability derived internally; coefficients `2,4` and `1,4,8` match. Core endpoint `concrete_theoremOneNine` at [ConcreteTheoremOneNine.lean:314](../GinibrePoincare/Endgame/ConcreteTheoremOneNine.lean#L314) avoids relying only on an abstract graph-domain assertion. |
| [Theorem 1.10, (1.46), (1.47)](https://arxiv.org/html/2608.19358v2#S1.SS8): derivative deficits and inverse root | Verified | `fullTheoremOneTenSchwartz`, `ginibreDifferentialDeficitVector`, `ginibreDifferentialSecondEnergy_eq_integral` in [FullTheoremOneTen.lean:184](../GinibrePoincare/Endgame/FullTheoremOneTen.lean#L184), lines 23 and 108. Actual Gaussian measure; ordinary Schwartz derivatives; coefficients `4/n`, `8/n`; actual centered transform and positive-mode projection. |
| Theorem 1.10: independent differential proof | Verified as alternative closure route | `bochnerKodairaTheoremOneTen` in [BochnerKodairaTheoremOneTen.lean:57](../GinibrePoincare/Endgame/BochnerKodairaTheoremOneTen.lean#L57); actual first weak-pair deficit at line 22. Finding 5 qualifies general operator-core proof fidelity. |
| Additional affine equality classification | Verified domain extension | `fullTheoremOneNine`/`fullTheoremOneTen` assert equality iff an almost-everywhere affine function of coordinate sum; this is stronger than the two deficit theorem statements themselves. |
| [Theorem 1.12, (1.50)](https://arxiv.org/html/2608.19358v2#S1.E50): radial core and Sobolev closure | Verified, with representation translation | `radial_core_lsi`, `radial_sobolev_lsi` in [FullRadialLSIReduction.lean:53](../GinibrePoincare/Analysis/FullRadialLSIReduction.lean#L53), line 60. Core includes all globally smooth compact symmetric radial functions, expressed via an arbitrary squared-radius witness; the paper's compact positive-radius profiles extend by zero and belong to this core. Closure is the actual value/gradient L² closure, not an assumed energy certificate. |
| [Theorem 1.13, (1.54)](https://arxiv.org/html/2608.19358v2#S1.E54): variance and entropy | Verified finite-overlap result; literal H¹ correspondence related | `fullMatrixLift_functional_inequalities` in [FullMatrixLift.lean:14](../GinibrePoincare/Endgame/FullMatrixLift.lean#L14). C¹ symmetric observable, Ginibre L² value and integrable actual overlap; coefficients `2/n`, `4/n`. Finding 1 applies to literal H¹ hypothesis. |
| Theorem 1.13: labeling and eigenvector-normalization invariance | Verified algebraic claims | `matrixOverlapEnergy_relabel`, `matrixOverlap_rescale` in [MatrixOverlap.lean:105](../GinibrePoincare/Analysis/MatrixOverlap.lean#L105), line 159. Actual intrinsic lift is independent of local ordering by symmetry. |
| [Theorem 1.14, (1.61)–(1.64)](https://arxiv.org/html/2608.19358v2#S1.SS10): measure, hypotheses and both inequalities | Verified on compact smooth stated core | `potentialWeight`, `potentialPartition`, `potentialMeasure`, `IsRhoConvexPotential`, `IsRhoSubharmonicPotential`, `NonQuadraticPotentialTheorem` in [NonQuadraticPotential.lean:29](../GinibrePoincare/Analysis/NonQuadraticPotential.lean#L29), lines 37, 41, 50, 55, 69; `fullNonQuadraticPotentialTheorem` in [FullNonQuadraticPotential.lean:12](../GinibrePoincare/Endgame/FullNonQuadraticPotential.lean#L12). Exact ordinary-gradient coefficients `1/(ρn)` and `2/(ρn)`; C² rotational potential, finite partition, positive ρ. Subharmonicity uses its C² Laplacian characterization `ΔV≥2ρ`. |
| Theorem 1.14: positive partition and recovery of quadratic case | Verified measure identity; specialization consequence | Actual positivity and probability proofs are internal. `potentialWeight_quadratic` in [NonQuadraticPotential.lean:96](../GinibrePoincare/Analysis/NonQuadraticPotential.lean#L96) identifies the weight; setting ρ=2 yields the asserted constants. This is not a sharpness claim for arbitrary V. |
| Problems 1.11, 1.15, 1.16; Appendix C | Excluded | Open research questions and numerical experiments. No unrestricted symmetric LSI, arbitrary-temperature or higher-dimensional solution is inferred. |

## Displayed and unnumbered proof calculations

| Paper anchors / assertions | Status | Correspondence |
| --- | --- | --- |
| [(1.29), (1.30)](https://arxiv.org/html/2608.19358v2#S1.E29): symmetrized and Wirtinger generator | Related exact display | Actual complex pregenerator and differential action were inspected through `PolynomialEigenfunctionGenerator` and `SumRadiusGenerator`; this review did not identify both literal displayed coordinate formulas as standalone endpoints. Symmetry and concrete sector action are verified. |
| Section 1.7: failure to preserve all symmetric polynomials | Related | Finding 4. |
| [(1.37), (1.40)](https://arxiv.org/html/2608.19358v2#S1.E37): Hamiltonian and confinement/interaction split | Verified definitions | Actual `ginibreHamiltonian` and `ginibreInteractionPotential`; Euclidean gradient/Laplacian use physical real coordinate directions. |
| [(1.38)](https://arxiv.org/html/2608.19358v2#S1.E38): pointwise Γ and Γ₂ | Verified | `ginibrePointwiseGamma_eq`, `ginibrePointwiseGammaTwo_bochner_bilinear` in [GinibrePointwiseBochner.lean:25](../GinibrePoincare/Analysis/GinibrePointwiseBochner.lean#L25), line 137. Actual operator-defined Γ₂, not a Hessian-only replacement definition. |
| Section 1.8: Bochner commutation | Verified generic differential identity | `bochnerCoordinateOperator_directional_commutation` in [GinibrePointwiseBochnerOperator.lean:33](../GinibrePoincare/Analysis/GinibrePointwiseBochnerOperator.lean#L33); specialization is used internally for actual Γ₂. |
| [(1.39)](https://arxiv.org/html/2608.19358v2#S1.E39): integrated Γ and Γ₂ identities | Γ verified by energy definition; Γ₂ related | Finding 2. |
| Lemma 1.7 proof: pair Hessian and tangential blowup | Verified directional equivalent | `ginibreHamiltonian_directional_hessian` in [GinibrePointwiseCurvatureTangent.lean:14](../GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean#L14), then explicit close-pair constructions. The exact 2×2 tensor notation is translated into directional quadratic forms. |
| [(1.42)](https://arxiv.org/html/2608.19358v2#S1.E42): integrated curvature bound | Verified forward bound | `ginibreFullGenerator_integrated_curvature` in [GinibreFullSemigroupDeficitConsequences.lean:29](../GinibrePoincare/Analysis/GinibreFullSemigroupDeficitConsequences.lean#L29). The general abstract converse equivalence with Poincaré was not separately reviewed. |
| [(1.43)](https://arxiv.org/html/2608.19358v2#S1.E43): interaction-only deficit formula and failure of pointwise positivity | Related consequence | Full Hamiltonian Bochner formula and confinement Hessian are proved; literal subtraction formula and an actual compact-test negativity witness were not identified. |
| [(1.48), (1.49)](https://arxiv.org/html/2608.19358v2#S1.E49): entropy convention and LSI linearization | Verified definitions and bounded linearization | `squareEntropy` uses literal real `f² log f²` and `Real.log 0=0`; `squareEntropy_affine_bound_variance` in [SquareEntropyLinearization.lean:162](../GinibrePoincare/Analysis/SquareEntropyLinearization.lean#L162) supplies a genuine bounded-observable perturbative implication. Existence of unrestricted Ginibre LSI remains open. |
| Section 1.9: simple spectrum and measurable labels | Verified | `matrixGaussian_charpoly_separable_ae`; `matrix_exists_measurable_simple_labeling` in [MatrixLocalSpectrum.lean:69](../GinibrePoincare/Analysis/MatrixLocalSpectrum.lean#L69). |
| [(1.51)–(1.53)](https://arxiv.org/html/2608.19358v2#S1.E51): projectors, overlap Gram matrix, positivity | Verified | `matrixRankOneProjector_biorthogonal`, `matrixOverlap_eq_gram`, `matrixOverlap_isHermitian`, `matrixOverlap_posSemidef`, `matrixOverlapEnergy_eq_HS` in [MatrixOverlap.lean:180](../GinibrePoincare/Analysis/MatrixOverlap.lean#L180), lines 35, 52, 47, 76. |
| [(1.55), (1.56)](https://arxiv.org/html/2608.19358v2#S1.E55): perturbation differential and chain rule | Verified on actual simple spectrum | `matrixLocalLabeling_fderiv`, `matrixLocalSpectralLift_fderiv` in [MatrixSpectralLiftDifferential.lean:14](../GinibrePoincare/Analysis/MatrixSpectralLiftDifferential.lean#L14), line 39; local differentiable branches are constructed in `MatrixLocalSpectrum`, not assumed at the assembled endpoint. |
| [(1.57)](https://arxiv.org/html/2608.19358v2#S1.E57): gradient energy factor 4 | Verified | `matrixSymmetricLift_energy` in [MatrixSymmetricLift.lean:43](../GinibrePoincare/Analysis/MatrixSymmetricLift.lean#L43), with `matrixLiftGradient_energy` in [MatrixOverlap.lean:131](../GinibrePoincare/Analysis/MatrixOverlap.lean#L131). |
| [(1.58), (1.59)](https://arxiv.org/html/2608.19358v2#S1.E58): Gaussian inequalities | Verified | Actual matrix Gaussian Poincaré and LSI on the compact-gradient closure in `MatrixGaussianPoincare` and `MatrixGaussianH1Closure`; constants `1/(2n)` and `1/n`. |
| [(1.60)](https://arxiv.org/html/2608.19358v2#S1.E60): spectral-law variance/entropy transfer | Verified | `matrixSpectralLift_integral`, `matrixSpectralLift_square_integral`, `matrixSpectralLift_squareEntropy` in [MatrixSpectralIntegralTransport.lean:37](../GinibrePoincare/Analysis/MatrixSpectralIntegralTransport.lean#L37), lines 57, 65. Actual Gaussian spectral law, no supplied Ginibre-law argument at these endpoints. |
| Section 1.9: no ordinary-energy comparison inferred; normal-matrix special case | Verified qualification; orthonormal case verified | `matrixOverlap_orthonormal`, `matrixOverlapEnergy_orthonormal` in [MatrixOverlap.lean:223](../GinibrePoincare/Analysis/MatrixOverlap.lean#L223), line 231. No general overlap bound is assumed. |
| [(1.65)](https://arxiv.org/html/2608.19358v2#S1.E65): nonquadratic radius density and Kostlan product | Verified via squared-radius representation | `rawPotentialSquaredRadiusLaw`, `potentialKostlanCoordinateLaw_squaredRadius`, `potential_radial_expectation_eq_squaredRadiusProduct` in [NonQuadraticRadiusLaw.lean:72](../GinibrePoincare/Analysis/NonQuadraticRadiusLaw.lean#L72), lines 127, 196; map `sqrt` gives actual radius law in `AlternativeBakryEmeryRadiusLaw`. Index `k` in Lean denotes paper `k+1`. |
| Section 1.10 proof: weighted complex estimate and phase projection | Verified assembled route | `rhoSubharmonic_potential_compact_poincare` in [GeneralPotentialSharpPoincare.lean:15](../GinibrePoincare/Analysis/GeneralPotentialSharpPoincare.lean#L15) applies internally proved quotient projection gap and centered positive phase geometry; no completion argument remains. |
| Section 1.10 proof: convex/nondecreasing radial remainder and arbitrary-dimensional lift | Verified | `bakryEmeryRadialRemainder_convex`, `even_convex_monotoneOn_nonnegative`, `bakryEmeryEuclideanLift_strongConvex` in [AlternativeBakryEmeryConvexLift.lean:23](../GinibrePoincare/Analysis/AlternativeBakryEmeryConvexLift.lean#L23), lines 40, 84. |
| Section 1.10 proof: primary strongly convex Gibbs LSI | Verified as expanded cited ingredient | `bakryEmeryConfigurationGibbs_square_lsi` in [AlternativeBakryEmeryConvexGibbsLSI.lean:12](../GinibrePoincare/Analysis/AlternativeBakryEmeryConvexGibbsLSI.lean#L12), actual normalized Gibbs density, internally constructed Brownian family and diffusion, no process/invariance input. This proves the needed finite-dimensional strongly convex estimate, not a universal abstract Γ₂ criterion. |
| Section 1.10 proof: regularization, limit and Lipschitz radius pushforward | Verified | `bakryEmeryEuclideanLift_square_lsi` in [AlternativeBakryEmeryLiftLSILimit.lean:70](../GinibrePoincare/Analysis/AlternativeBakryEmeryLiftLSILimit.lean#L70), and `bakryEmery_kostlan_radius_bounded_lsi` in [AlternativeBakryEmeryRadialLSI.lean:12](../GinibrePoincare/Analysis/AlternativeBakryEmeryRadialLSI.lean#L12). Actual gradient identity off the null origin; Gaussian domination proves entropy/energy limits. |
| Section 1.10 proof: tensorization and gradient transfer | Verified | `bakryEmery_radiusProduct_lsi_of_factor_lsi` in [AlternativeBakryEmeryRadialProductAssembly.lean:99](../GinibrePoincare/Analysis/AlternativeBakryEmeryRadialProductAssembly.lean#L99) is explicitly a reduction; actual factor inputs are discharged by `AlternativeBakryEmeryRadialProductLSI`, then `bakryEmery_potential_smooth_radial_lsi` in [AlternativeBakryEmeryPotentialRadialLSI.lean:34](../GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLSI.lean#L34). |
| [(5.1)–(5.5)](https://arxiv.org/html/2608.19358v2#S5): sector coordinate calculus | Verified differential equivalent | `fderiv_sumRadiusPolynomial` in [SumRadiusCoordinates.lean:94](../GinibrePoincare/Analysis/SumRadiusCoordinates.lean#L94); private `polynomial_laplacian`, `polynomial_confinement`, `polynomial_coulomb` in [SumRadiusGenerator.lean:19](../GinibrePoincare/Analysis/SumRadiusGenerator.lean#L19), lines 72, 85, and public assembled generator at line 100. This is ordinary real directional calculus translating the paper's Wirtinger display. |
| [(5.6), (5.7)](https://arxiv.org/html/2608.19358v2#S5.E6): Hermite/Laguerre eigen-equations | Verified | `polynomialEigenfunction_generator` in [PolynomialEigenfunctionGenerator.lean:49](../GinibrePoincare/Analysis/PolynomialEigenfunctionGenerator.lean#L49) combines actual Hermite and Laguerre polynomial equations; `radial_laguerre_equation` in [PolynomialEigenfunctions.lean:102](../GinibrePoincare/Analysis/PolynomialEigenfunctions.lean#L102). |
| Section 5: triangular bases and factorized orthogonality | Verified | `PolynomialEigenfunctionSpan`, `PolynomialEigenfunctionBasis`, `PolynomialEquilibriumOrthogonality`; actual algebraic basis rather than a density claim in full symmetric L². |
| [(6.1)](https://arxiv.org/html/2608.19358v2#S6.E1): energy/dissipation and centering | Verified actual graph identity | `ginibreFullGenerator_dissipation_eq_energy` in [GinibreFullSemigroupDeficitConsequences.lean:14](../GinibrePoincare/Analysis/GinibreFullSemigroupDeficitConsequences.lean#L14), actual core IBP and weak-pair centering. |
| [(6.2)](https://arxiv.org/html/2608.19358v2#S6.E2): mode expansion and permutation invariance | Verified | `hasSum_gaussianHermiteMode`, `gaussianPermutationL2_comm_gaussianHermiteMode`, `gaussianHermiteMode_mem_alternating` in [HermiteParsevalModes.lean:73](../GinibrePoincare/Analysis/HermiteParsevalModes.lean#L73), lines 348, 357. |
| [(6.3), (6.4)](https://arxiv.org/html/2608.19358v2#S6.E3): weighted mode energy and lowering transfer | Verified | `concrete_weightedModeEnergy` in [ConcreteTheoremOneNine.lean:132](../GinibrePoincare/Endgame/ConcreteTheoremOneNine.lean#L132), with actual ground-state and weak derivative coefficient bridges. |
| [(6.5)](https://arxiv.org/html/2608.19358v2#S6.E5): zero-mode norm and holomorphic splitting | Verified | `concreteZeroMode_norm_sq_eq_holomorphicProjection` in [ConcreteTheoremOneNine.lean:242](../GinibrePoincare/Endgame/ConcreteTheoremOneNine.lean#L242); weak version `ginibreFullWeak_zero_mode_norm` in [GinibreEqualityWeakDeficit.lean:66](../GinibrePoincare/Analysis/GinibreEqualityWeakDeficit.lean#L66). |
| [(6.6)](https://arxiv.org/html/2608.19358v2#S6.E6): algebraic second deficit | Verified | `ginibreGenerator_second_deficit_algebra` in [GinibreGeneratorDeficitAlgebra.lean:20](../GinibrePoincare/Analysis/GinibreGeneratorDeficitAlgebra.lean#L20). |
| [(6.7)–(6.9)](https://arxiv.org/html/2608.19358v2#S6.E7): number energy, adjoint, commutator and integrated identity | Verified on concrete compact/closed-jet routes | `bkCompact_commutator`, `bkCompact_integrated_identity` in [AlternativeBochnerKodairaCompact.lean:57](../GinibrePoincare/Analysis/AlternativeBochnerKodairaCompact.lean#L57), line 98; `bkGaussian_number_pair`, `bkGaussian_integrated_identity` in [AlternativeBochnerKodairaIdentity.lean:15](../GinibrePoincare/Analysis/AlternativeBochnerKodairaIdentity.lean#L15), line 64. Both IBP operations are proved. |
| Section 6 after (6.9): compact operator core, kernel, spectral support, invertibility | Related literal general operator assertions | Finding 5. Entire-space identification exists elsewhere; particular inverse-root closure is concrete. This review does not equate those facts with all general operator statements in that paragraph. |
| [(6.10)–(6.12)](https://arxiv.org/html/2608.19358v2#S6.E10): transform energy, projection norms and removal of holomorphic energy | Verified for actual weak pair | `ginibreFullWeak_holomorphic_geometry`, `ginibreFullWeak_zero_mode_norm` in [GinibreEqualityWeakDeficit.lean:40](../GinibrePoincare/Analysis/GinibreEqualityWeakDeficit.lean#L40), line 66; actual transformed coefficient equations used in `bochnerKodaira_ginibre_weak_first_deficit`. |
| [(6.13), (6.14)](https://arxiv.org/html/2608.19358v2#S6.E13): spectral square-root expression | Related literal spectral calculus; exact resulting deficit verified | The assembled route proves the derivative square directly from finite number-operator identities and bounded synthesis. No literal `(N−nI)^(1/2)` general functional-calculus bridge was independently identified. |
| [(6.15), (6.16)](https://arxiv.org/html/2608.19358v2#S6.E15): inverse root and second derivative sum | Verified concrete inverse-root vector and norm identity | `ginibreDifferentialDeficitVector`; `bkInverseSquareRoot_total_energy` in [AlternativeBochnerKodairaInverseRoot.lean:117](../GinibrePoincare/Analysis/AlternativeBochnerKodairaInverseRoot.lean#L117). Particular vector approximation replaces the general operator-core proof route. |
| [(7.1)](https://arxiv.org/html/2608.19358v2#S7.E1): Kostlan radii and Gamma/block laws | Verified | `ginibre_magnitude_expectation_eq_gamma` in [RadialMagnitudeProfile.lean:68](../GinibrePoincare/Analysis/RadialMagnitudeProfile.lean#L68), exact scaled squared-radius/Gamma laws and block-law representation. |
| [(7.2)](https://arxiv.org/html/2608.19358v2#S7.E2): sharp Gaussian block LSI | Verified | `gaussianBlock_lsi`, invoked without an LSI argument by `radial_core_lsi`; actual covariance `(2n)⁻¹`, coefficient `1/n`. |
| [(7.3), (7.4)](https://arxiv.org/html/2608.19358v2#S7.E3): block gradient and radius product bound | Verified equivalent block formulation | `hasFDerivAt_blockMagnitudes`, `blockGradientNormSq_magnitude` in [BlockMagnitudeGradient.lean:18](../GinibrePoincare/Analysis/BlockMagnitudeGradient.lean#L18), line 60; actual compact Lipschitz block lift avoids a smoothness assertion at zero. The literal displayed product-radius endpoint was not separately located. |
| [(7.5)](https://arxiv.org/html/2608.19358v2#S7.E5): entropy transport | Verified | `ginibre_magnitude_entropy_eq_block` in [BlockMagnitudeLift.lean:89](../GinibrePoincare/Analysis/BlockMagnitudeLift.lean#L89). |
| [(7.6), (7.7)](https://arxiv.org/html/2608.19358v2#S7.E6): radial gradient identity, symmetry and energy transport | Verified | `realGradientNormSq_magnitude`, `magnitudeEnergyDensity_symmetric` in [MagnitudeGradient.lean:56](../GinibrePoincare/Analysis/MagnitudeGradient.lean#L56), line 77; `ginibre_magnitude_energy_eq_block` in [BlockMagnitudeLift.lean:104](../GinibrePoincare/Analysis/BlockMagnitudeLift.lean#L104). Nonzero-coordinate exceptions proved null. |
| Section 7 final paragraph: H¹ closure and entropy lower semicontinuity | Verified concrete closure | `radialSobolevClosure_lsi_of_core` in [RadialSobolevClosure.lean:96](../GinibrePoincare/Analysis/RadialSobolevClosure.lean#L96), applied unconditionally in `radial_sobolev_lsi`. Entropy integrability is obtained, not assumed. |

## Review limits

The main requested numbered conclusions in this partition have matching
concrete endpoint statements, except for the unclosed literal H¹-domain
identification in Theorem 1.13. The table records additional display/proof
correspondence questions separately. It deliberately does not claim all
cited external models, every explanatory sentence, every general spectral
calculus assertion, or all local declarations were independently reviewed.
No new build or axiom audit was run by this reviewer; existing mechanical
evidence must retain its own snapshot and timestamp. Registry publication
was not part of this agent's assignment and is not established here.
