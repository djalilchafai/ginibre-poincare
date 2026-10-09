# Sharp inequalities and exact deficits

[Reading index](../../HUMAN_READABILITY.md) · [Verified revision and current evidence](../../STATUS.md)

## Theorem 1.1: sharp Poincaré and equality

Read these modules in order, stopping at the relevant declaration rather than
reading every helper.

1. [Configuration](../../GinibrePoincare/Concrete/Configuration.lean) and
   [MainProofReduction](../../GinibrePoincare/Concrete/MainProofReduction.lean)
   fix configurations, symmetric observables and the five statements consumed
   by the original analytic proof.
2. [GroundStateDbar](../../GinibrePoincare/Analysis/GroundStateDbar.lean)
   supplies `groundStateAdmissibility` and `groundStateEnergyIdentity`.
   Multiplication by the normalized Vandermonde moves the interaction density
   into the observable, so the next estimates live in Gaussian L².
3. [GaussianEntireDistance](../../GinibrePoincare/Analysis/GaussianEntireDistance.lean)
   gives the Gaussian dbar distance estimate. Read
   [GinibreEntireProjectionEndpoints](../../GinibrePoincare/Analysis/GinibreEntireProjectionEndpoints.lean)
   for `groundStateDistanceIdentityStatement` and `ginibreHalfDistanceStatement`:
   these identify the actual representative distance infima and provide the
   geometric factor needed to turn the Gaussian estimate into the sharp bound.
4. [FullMainAnalyticProof](../../GinibrePoincare/Endgame/FullMainAnalyticProof.lean)
   assembles these five ingredients into `fullMainAnalyticProof`. This endpoint
   is the smooth compact symmetric version.
5. [GinibreArbitraryWeakPairClosure](../../GinibrePoincare/Analysis/GinibreArbitraryWeakPairClosure.lean)
   is the approximation bridge. Then read
   [GinibreSymmetricWeakPoincare](../../GinibrePoincare/Analysis/GinibreSymmetricWeakPoincare.lean),
   especially `ginibre_symmetric_weak_poincare`. Its variance is the squared
   centered L² norm and `ginibreWeakEnergy` is `(1/n) * ‖g‖²`. Thus the sharp
   statement is `variance ≤ energy / 2`.
6. [GinibreEqualityWeakAffine](../../GinibrePoincare/Analysis/GinibreEqualityWeakAffine.lean)
   proves `ginibreEquality_full_weak_affine_iff`. The forward proof reconstructs
   the holomorphic part, removes higher conjugate modes, identifies the first
   quotient with `c * coordinateSum`, then restores the mean. Equality is
   almost everywhere with `a + 2 * (c * coordinateSum z).re`.

The equality proof covers the weak domain. It should not be read as a
classification only among polynomials. Conversely, the compact smooth endpoint
alone does not supply that classification.

For independent routes, start with
[AlternativeSpectralPoincare](../../GinibrePoincare/Analysis/AlternativeSpectralPoincare.lean)
or [AlternativeSlaterPoincare](../../GinibrePoincare/Analysis/AlternativeSlaterPoincare.lean).
The former uses number forms and the Vandermonde factorization; the latter uses
a determinant expansion and degree energy. The route-specific qualifications
are retained in [REPORT.md](../../REPORT.md#independent-proof-routes-and-domain-qualifications).

## Theorems 1.9 and 1.10: exact deficits

Use [FullTheoremOneNine](../../GinibrePoincare/Endgame/FullTheoremOneNine.lean)
as a statement map. The input pair `(u,v)` belongs to the real symmetric generator
graph. The conclusion produces a genuine weak gradient `g`, summable mode
energy, two exact identities, and the weak affine equality classification.
The tuple order follows those mathematical roles. For application proofs,
`fullTheoremOneNine_named` returns the same conclusions as the
`GinibreGeneratorDeficits` record, so each fact has a mathematical name.
Within a proof with the endpoint hypotheses in scope:

```lean
obtain ⟨g, result⟩ := fullTheoremOneNine_named hn u v hgraph
have hdeficit := result.poincare_deficit
have hequality := result.equality_iff_affine
```

`ginibreCenteredHermiteMass hn u.val` abbreviates the repeated centered
transform/mode-mass expression. It carries the same definition and normalization.

For the proof, follow
[GinibreFullGeneratorDeficit](../../GinibrePoincare/Analysis/GinibreFullGeneratorDeficit.lean)
through its imports, then
[GinibreFullSemigroupDeficitConsequences](../../GinibrePoincare/Analysis/GinibreFullSemigroupDeficitConsequences.lean).
The latter explains the operator interpretation:
`ginibreFullGenerator_dissipation_eq_energy` identifies energy with the negative
pairing of the generator output and the centered input. Nonnegativity of the
squared remainder and tail then gives integrated curvature; its equality
statement identifies the spectral-gap generator equation.

Keep four objects distinct:

| Lean expression | Mathematical role |
| --- | --- |
| `ginibreFullCenter ... u.val` | Subtract the Ginibre mean |
| `ginibreFullCenteredTransform ... u.val` | Center, then transfer to Gaussian L² |
| `ginibreFullHolomorphicRemainder ... u.val` | Geometric remainder appearing in both identities |
| `positiveHermiteModeMass ... k` and `modeTail` | Squared Gaussian mode masses and their weighted excess |

The first identity has coefficients `2` on the geometric squared norm and `4`
on the mode tail. The second has the shifted generator squared norm, coefficient
`4` on the geometric remainder and `8` on the tail. An operator norm identity
and a literal integral of pointwise Γ₂ require a bridge; read
[FullTheoremOneNinePointwiseGamma](../../GinibrePoincare/Endgame/FullTheoremOneNinePointwiseGamma.lean)
and [CorrespondenceOperatorUnrestrictedGamma](../../GinibrePoincare/Analysis/CorrespondenceOperatorUnrestrictedGamma.lean)
for the relevant domains and integral identification.

Next read [FullTheoremOneTen](../../GinibrePoincare/Endgame/FullTheoremOneTen.lean).
Its definition `ginibreDifferentialDeficitVector` subtracts mode zero from the
centered transform and applies the Gaussian inverse square root. The first and
second derivative fields are synthesized from the transformed weak gradient.
`ginibreDifferentialDeficit_weak_derivatives` proves that these are derivatives,
not merely coefficient formulas. `ginibreDifferentialSecondEnergy_eq_tail`
identifies their total energy with `n * modeTail`; this is precisely why the
coefficients become `4/n` and `8/n` in `fullTheoremOneTen`.

`ginibreDifferentialSecondEnergy_eq_integral` replaces each squared L² norm by
a Gaussian integral of `Complex.normSq`. `fullTheoremOneTenSchwartz` then uses
`gaussianSchwartzDbar_iff_weak` to state the result with ordinary distributional
derivatives. These are distinct bridges worth reading before treating a
weighted derivative graph as ordinary differentiation.

The independently assembled Bochner route starts with
[AlternativeBochnerKodairaDifferential](../../GinibrePoincare/Analysis/AlternativeBochnerKodairaDifferential.lean):
real directional derivatives define the Wirtinger operators; product and
commutation identities yield `bkDbar_adjoint_comm`. Continue through
[AlternativeBochnerKodairaCompact](../../GinibrePoincare/Analysis/AlternativeBochnerKodairaCompact.lean)
and [AlternativeBochnerKodairaClosure](../../GinibrePoincare/Analysis/AlternativeBochnerKodairaClosure.lean)
to [BochnerKodairaTheoremOneTen](../../GinibrePoincare/Endgame/BochnerKodairaTheoremOneTen.lean).
This explains the differential identity through adjoint integration and closure,
whereas the first route converts the already established Hermite deficits.

For the differential result, the parallel record `GinibreDifferentialDeficits`
allows direct access to the derivative assertions. With the same input context:

```lean
obtain ⟨g, result⟩ := fullTheoremOneTen_named hn u v hgraph
have hfirst := result.first_derivatives
have hsecond := result.second_derivatives
have hdeficit := result.poincare_deficit
```

These records are conclusions of the existing proofs. They keep the same domain
hypotheses and provide a readable way to consume the result.
