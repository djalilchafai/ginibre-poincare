# Domains and analytic foundations

[Reading index](../../HUMAN_READABILITY.md) · [Verified revision and current evidence](../../STATUS.md)

## Domains and cores

There are several levels of domain. They answer different mathematical questions.

| Interface | What to check when reading |
| --- | --- |
| Smooth compact core | Differentiability, support and collision-free qualification |
| `IsGinibreDistributionalGradient` | An actual compact-test weak derivative, with L² value and gradient |
| Symmetric weak pair | Permutation invariance of the value and the corresponding gradient |
| Generator graph `(u,v)` | Domain membership plus the operator output; permits a squared output norm |
| Closure of a core | Which norm or joint graph is completed, and the theorem connecting it to ordinary weak derivatives |

Read [GinibreSmoothDistributionalGradient](../../GinibrePoincare/Analysis/GinibreSmoothDistributionalGradient.lean)
for smooth-to-weak identification and
[GinibreArbitraryWeakPairClosure](../../GinibrePoincare/Analysis/GinibreArbitraryWeakPairClosure.lean)
for approximation of arbitrary weak pairs. The exact generator/weak-form bridge
appears through
[GinibreFullGeneratorDeficit](../../GinibrePoincare/Analysis/GinibreFullGeneratorDeficit.lean)
and its imported graph-identification lemmas.

Appendix A's comparison of cores has two separate ingredients:
[GinibreGraphNormEquivalence](../../GinibrePoincare/Analysis/GinibreGraphNormEquivalence.lean)
compares the positive-speed norms, while
[GinibreRealCoreClosureEquivalence](../../GinibrePoincare/Analysis/GinibreRealCoreClosureEquivalence.lean)
and [GinibreComplexCoreClosureEquivalence](../../GinibrePoincare/Analysis/GinibreComplexCoreClosureEquivalence.lean)
identify global and collision-free compact smooth gradient graph closures.
An equality of completed domains needs these bridges; membership in an abstract
completion alone does not explain which ordinary functions belong to it.

## Pointwise curvature and collision capacity

[GinibrePointwiseCurvature](../../GinibrePoincare/Analysis/GinibrePointwiseCurvature.lean)
first computes the imaginary-coordinate Hessian at a real configuration. An
inverse squared particle separation appears with negative sign. Collapsing a
pair makes the pointwise curvature unbounded below. The mean curvature is a
separate Hamiltonian Hessian conclusion.
[GinibrePointwiseCurvatureTangent](../../GinibrePoincare/Analysis/GinibrePointwiseCurvatureTangent.lean)
extends the Hessian calculation to arbitrary directions and a center-zero
pair direction. These explain why a positive integrated bound cannot be read as
a uniform positive pointwise curvature bound.

[GinibreCollisionCapacity](../../GinibrePoincare/Analysis/GinibreCollisionCapacity.lean)
defines `ginibreCapacityCosts` using representatives at least one on an open
neighborhood, their actual weak gradients, and the weighted H¹ cost.
`ginibreCollisionSet_capacity_zero` concerns the infimum of those costs.
Read the cutoff exhaustion import for the approximating functions: the crucial
point is that both the L² cost and the Dirichlet cost tend to zero. Measure-zero
collisions alone would not establish capacity zero or justify removing collisions
from a Sobolev core.

## Gaussian and complex foundations

Begin with [ComplexHermite](../../GinibrePoincare/Analysis/ComplexHermite.lean),
[ComplexHermiteOrthogonality](../../GinibrePoincare/Analysis/ComplexHermiteOrthogonality.lean)
and [ComplexHermiteLowering](../../GinibrePoincare/Analysis/ComplexHermiteLowering.lean)
for the polynomial basis, its norms and the Wirtinger lowering relations.
The relevant completeness and closure modules are reached from
[GaussianDbarWeakEquality](../../GinibrePoincare/Analysis/GaussianDbarWeakEquality.lean).
Its `gaussianWeakDbar_energy_series` identifies the derivative energy with the
weighted mode series; `gaussianWeakDbar_gap` and its equality theorem extract
the gap and low-mode geometry. Later endpoints explicitly convert to ordinary
volume and Schwartz distributional derivatives.

[GaussianCanonicalDbarSolution](../../GinibrePoincare/Analysis/GaussianCanonicalDbarSolution.lean)
defines the solution as `u` minus its orthogonal projection onto the actual
entire closed space. The proof then checks three things: the projection has
zero dbar derivative, subtraction preserves the prescribed derivative, and
Pythagoras gives minimum norm and uniqueness. Read
`gaussianCanonicalDbarSolution_schwartz`,
`gaussianCanonicalDbarSolution_pythagoras`, and
`gaussianCanonicalDbarSolution_minimal`. The solver's definition by projection
is useful only because these compatibility and minimality facts are proved.

[EntireVandermondeFactorization](../../GinibrePoincare/Analysis/EntireVandermondeFactorization.lean)
is best read from the local step to the endpoint:

1. `collisionLinearForm` represents a particle difference as a continuous
   complex-linear map.
2. `entire_linearDivision_preserves_hyperplane_zero` shows that dividing by one
   collision factor preserves vanishing on the other transverse hyperplanes.
3. `entire_division_collisionFactors` iterates division over finitely many pairs.
4. `collisionPairs_product_eq_vandermonde` identifies the product of factors.
5. `entire_alternating_vandermonde_factorization` gives the global entire
   factorization, followed by the Gaussian L² representative version.

This route makes the role of alternation concrete: it forces vanishing on each
collision hyperplane, which permits successive entire division. It also explains
why an almost-everywhere L² identity needs an entire representative theorem
before pointwise complex analysis can be applied.

## Maximal number-domain Bochner data

[CorrespondenceOperatorNumberBochnerClosure](../../GinibrePoincare/Analysis/CorrespondenceOperatorNumberBochnerClosure.lean)
starts with finite Hermite graph approximations. A second-derivative norm bound
in terms of the number image makes the derivative sequences Cauchy. Their L²
limits are identified by closedness of the weak derivative graph, then finite
energy identities pass to the limit. This supplies second derivatives from
maximal number-domain membership without an additional regularity argument.

`GaussianNumberBochnerData` contains the first and second derivative vectors,
their weak derivative laws, and `energy_identity`. It is a data structure;
`correspondenceOperatorNumber_has_bochner_data` proves it is inhabited. With the
Gaussian graph pair `u v` and `huv` in scope, a proof can use:

```lean
obtain ⟨data⟩ := correspondenceOperatorNumber_has_bochner_data hn u v huv
have hFirst := data.first_weak
have hSecond := data.second_weak
have hEnergy := data.energy_identity
```

The identity is `‖v‖² = Σⱼₖ ‖second j k‖² + n Σⱼ ‖first j‖²`.
Here `v` is the Gaussian number-operator output. This data interface concerns
the maximal Gaussian number graph, whereas the Ginibre differential-deficit
record concerns the centered inverse-square-root vector. Their normalizations
and input spaces should be checked before transferring an identity between them.
