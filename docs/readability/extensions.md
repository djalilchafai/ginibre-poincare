# Radial, matrix and nonquadratic inequalities

[Reading index](../../HUMAN_READABILITY.md) · [Verified revision and current evidence](../../STATUS.md)

## Theorem 1.12: radial logarithmic Sobolev

Read [KostlanProductLaw](../../GinibrePoincare/Analysis/KostlanProductLaw.lean)
for the radius-law transfer and
[BlockMagnitudeLift](../../GinibrePoincare/Analysis/BlockMagnitudeLift.lean)
for the Gaussian block representation.
[GaussianBlockLSI](../../GinibrePoincare/Analysis/GaussianBlockLSI.lean)
supplies the Gaussian analytic inequality.

[FullRadialLSIReduction](../../GinibrePoincare/Analysis/FullRadialLSIReduction.lean)
shows how these pieces are used. `radial_core_lsi_of_gaussian` is a reusable
reduction with an explicit Gaussian LSI argument. The later `radial_core_lsi`
and `radial_sobolev_lsi` discharge it. The proof takes the observable's magnitude
profile, lifts it to Gaussian blocks, transfers entropy and energy, and then
passes to the Sobolev completion. The radial witness itself need not come with
regularity: regularity is recovered from the original smooth observable.
[LogSobolevInequality](../../GinibrePoincare/Analysis/LogSobolevInequality.lean)
exports the assembled inequality. The normalization is `Ent(f²) ≤ E`.

## Theorem 1.13: matrix lift and overlaps

Keep the eigenvalue law and the derivative formula separate. The matrix lift
must first have the Ginibre spectral pushforward law; the local derivative
formula then introduces eigenvector overlaps into the matrix gradient energy.

[FullMatrixLift](../../GinibrePoincare/Endgame/FullMatrixLift.lean) is a compact
entry point for the finite-overlap interface. It assumes a symmetric C¹
observable, Ginibre L² membership and integrability of the overlap energy under
the Gaussian matrix law. It combines
[MatrixSpectralLiftLSIFinite](../../GinibrePoincare/Analysis/MatrixSpectralLiftLSIFinite.lean)
with [MatrixSpectralLiftPoincareFinite](../../GinibrePoincare/Analysis/MatrixSpectralLiftPoincareFinite.lean).
The variance and entropy coefficients are respectively `2/n` and `4/n`.
`fullMatrixLift_named` packages these conclusions as `MatrixLiftInequalities`.
With the finite-overlap hypotheses in scope, application proofs can use:

```lean
have result := fullMatrixLift_named hn F hF hsym hFL2 hE
have hvariance := result.poincare
have hentropy := result.log_sobolev
```

The record also exposes `entropy_integrable`, needed when manipulating the
literal entropy integral.

For the paper's matrix H¹ interface, read
[CorrespondenceMatrixWeakClosure](../../GinibrePoincare/Analysis/CorrespondenceMatrixWeakClosure.lean)
in its declaration order:

1. `correspondenceMatrix_test_integral` converts Gaussian weighted test
   pairings to ordinary volume pairings using the strictly positive density.
2. `correspondenceMatrix_H1_weak` identifies the ordinary weak derivative.
3. `correspondenceMatrix_simple_isOpen` and
   `correspondenceMatrix_lift_contDiffOn` allow local classical differentiation
   on simple-spectrum charts.
4. `correspondenceMatrix_H1_local_derivative` and
   `correspondenceMatrix_H1_derivative` identify that derivative with the weak
   one, using almost-everywhere simple spectrum.
5. `correspondenceMatrix_theorem_1_13` packages the resulting inequalities from
   `MatrixGaussianH1Function`. Finite overlap energy is derived here.

For the direct Gaussian variance proof, inspect
[AlternativeMatrixPoincare](../../GinibrePoincare/Analysis/AlternativeMatrixPoincare.lean)
and [MatrixGaussianPoincare](../../GinibrePoincare/Analysis/MatrixGaussianPoincare.lean).

## Theorem 1.14: nonquadratic potentials

[NonQuadraticPotential](../../GinibrePoincare/Analysis/NonQuadraticPotential.lean)
is the definitions map: `potentialWeight`, `potentialPartition`,
`potentialMeasure`, rotational invariance, strong convexity and the literal
Laplacian lower bound. Some comments retain older theorem numbering; the paper's
v2 result is 1.14. The normalized measure uses the actual partition integral.
The endpoint requires C² regularity, rotational invariance, finite partition,
and `ρ > 0`; the two inequalities consume different lower bounds.

For Poincaré, read
[GeneralPotentialSharpPoincare](../../GinibrePoincare/Analysis/GeneralPotentialSharpPoincare.lean).
Its short proof exposes the three mathematical steps: centering puts the
holomorphic quotient in the positive sector; projection geometry bounds the
variance by twice the residual; the compact gap estimate bounds that residual
by gradient energy. The result is coefficient `1/(nρ)` under `ΔV ≥ 2ρ`.
Its imports point to the quotient closure and variance lemmas when a step needs
further explanation.

For radial LSI, start with
[AlternativeBakryEmeryConvexGibbsLSI](../../GinibrePoincare/Analysis/AlternativeBakryEmeryConvexGibbsLSI.lean),
then [AlternativeBakryEmeryLiftLSILimit](../../GinibrePoincare/Analysis/AlternativeBakryEmeryLiftLSILimit.lean),
[AlternativeBakryEmeryRadialProductLSI](../../GinibrePoincare/Analysis/AlternativeBakryEmeryRadialProductLSI.lean)
and [AlternativeBakryEmeryPotentialRadialLSI](../../GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLSI.lean).
The steps are strongly convex Gibbs LSI, regularized Euclidean lift, exact radius
laws, tensorization and transfer to interacting radial observables.

[FullNonQuadraticPotential](../../GinibrePoincare/Endgame/FullNonQuadraticPotential.lean)
assembles both branches. Strong convexity supplies radial LSI coefficient
`2/(nρ)` on the stated smooth compact radial domain. The bounded Lipschitz radial
extension is in
[AlternativeBakryEmeryPotentialRadialLipschitzLSI](../../GinibrePoincare/Analysis/AlternativeBakryEmeryPotentialRadialLipschitzLSI.lean).
An independent Gaussian quantile transport route starts with
[StrongConvexPotentialRadialLSI](../../GinibrePoincare/Analysis/StrongConvexPotentialRadialLSI.lean).
Do not transfer the quadratic full weak-domain equality classification to a
general potential without a separate theorem.
