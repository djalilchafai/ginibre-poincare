module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianFinite
public import Mathlib.Probability.Moments.Variance
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def bakryBrownianFiniteDyadicLinear (N : ℕ) (c : BakryBrownianFiniteDyadicIndex N → ℝ)
    (sample : BakryBrownianDyadicSample) : ℝ :=
  ∑ i, c i * sample (bakryBrownianFiniteDyadicEmbed N i)

theorem bakryBrownianFiniteDyadicLinear_gaussian (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    HasGaussianLaw (bakryBrownianFiniteDyadicLinear N c) bakryBrownianDyadicMeasure := by
  let L : (BakryBrownianFiniteDyadicIndex N → ℝ) →L[ℝ] ℝ :=
    ∑ i, c i • ContinuousLinearMap.proj i
  convert (bakryBrownianFiniteDyadic_coordinates_gaussian N).map_fun L using 1
  funext sample
  simp only [L, bakryBrownianFiniteDyadicLinear, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

theorem bakryBrownianFiniteDyadicLinear_mean (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    (∫ sample, bakryBrownianFiniteDyadicLinear N c sample ∂bakryBrownianDyadicMeasure) = 0 := by
  have hc (i : BakryBrownianFiniteDyadicIndex N) : Integrable
      (fun sample : BakryBrownianDyadicSample => c i * sample (bakryBrownianFiniteDyadicEmbed N i))
      bakryBrownianDyadicMeasure :=
    ((bakryBrownianDyadic_coordinate_law _).hasGaussianLaw.integrable).const_mul _
  unfold bakryBrownianFiniteDyadicLinear
  rw [integral_finsetSum _ (fun i _ => hc i)]
  apply Finset.sum_eq_zero
  intro i hi
  rw [integral_const_mul, (bakryBrownianDyadic_coordinate_law _).integral_eq, integral_id_gaussianReal, mul_zero]

theorem bakryBrownianFiniteDyadicLinear_variance (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    Var[bakryBrownianFiniteDyadicLinear N c; bakryBrownianDyadicMeasure] = ∑ i, (c i)^2 := by
  let X := fun i (sample : BakryBrownianDyadicSample) => c i * sample (bakryBrownianFiniteDyadicEmbed N i)
  have hMem (i : BakryBrownianFiniteDyadicIndex N) : MemLp (X i) 2 bakryBrownianDyadicMeasure :=
    ((bakryBrownianDyadic_coordinate_law _).hasGaussianLaw.memLp_two).const_mul _
  have hInd := (bakryBrownianDyadic_coordinates_independent.precomp
    (bakryBrownianFiniteDyadicEmbed_injective N)).comp (fun i x => c i*x) (fun i => by fun_prop)
  have he : bakryBrownianFiniteDyadicLinear N c = ∑ i, X i := by
    funext sample
    simp only [bakryBrownianFiniteDyadicLinear, Finset.sum_apply, X]
  rw [he, IndepFun.variance_sum (fun i _ => hMem i) (fun i _ j _ hij => hInd.indepFun hij)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [variance_const_mul, (bakryBrownianDyadic_coordinate_law _).variance_eq,
    variance_id_gaussianReal]
  simp

theorem bakryBrownianFiniteDyadicLinear_law (N : ℕ)
    (c : BakryBrownianFiniteDyadicIndex N → ℝ) :
    HasLaw (bakryBrownianFiniteDyadicLinear N c)
      (gaussianReal 0 (∑ i, (c i)^2).toNNReal) bakryBrownianDyadicMeasure := by
  have hg := bakryBrownianFiniteDyadicLinear_gaussian N c
  refine ⟨hg.aemeasurable,?_⟩
  rw [hg.map_eq_gaussianReal, bakryBrownianFiniteDyadicLinear_mean, bakryBrownianFiniteDyadicLinear_variance]

theorem bakryBrownianFiniteDyadicLinear_covariance (N : ℕ)
    (c d : BakryBrownianFiniteDyadicIndex N → ℝ) :
    cov[bakryBrownianFiniteDyadicLinear N c, bakryBrownianFiniteDyadicLinear N d;
      bakryBrownianDyadicMeasure] = ∑ i, c i*d i := by
  have he := variance_add (bakryBrownianFiniteDyadicLinear_gaussian N c).memLp_two
    (bakryBrownianFiniteDyadicLinear_gaussian N d).memLp_two
  have hAdd : bakryBrownianFiniteDyadicLinear N (c+d) =
      bakryBrownianFiniteDyadicLinear N c + bakryBrownianFiniteDyadicLinear N d := by
    funext sample
    simp only [bakryBrownianFiniteDyadicLinear, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [← hAdd, bakryBrownianFiniteDyadicLinear_variance,
    bakryBrownianFiniteDyadicLinear_variance, bakryBrownianFiniteDyadicLinear_variance] at he
  have hp : (∑ i, (c i+d i)^2) = (∑ i, (c i)^2)+2*(∑ i, c i*d i)+(∑ i, (d i)^2) := by
    simp only [add_sq, Finset.sum_add_distrib, mul_assoc,← Finset.mul_sum]
  change (∑ i, (c i+d i)^2) = _ at he
  linarith

#print axioms bakryBrownianFiniteDyadicLinear_covariance
#print axioms bakryBrownianFiniteDyadicLinear_gaussian
#print axioms bakryBrownianFiniteDyadicLinear_mean
#print axioms bakryBrownianFiniteDyadicLinear_variance
#print axioms bakryBrownianFiniteDyadicLinear_law
end
end GinibrePoincare
