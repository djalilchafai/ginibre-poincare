module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicCoordinates
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.Basic
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

abbrev BakryBrownianFiniteDyadicIndex (N : ℕ) := Option (Σ n : Fin N, Fin (2^n.val))

def bakryBrownianFiniteDyadicEmbed (N : ℕ) : BakryBrownianFiniteDyadicIndex N → BakryBrownianDyadicIndex
  | none => none
  | some ⟨n,k⟩ => some ⟨n.val,k⟩

theorem bakryBrownianFiniteDyadicEmbed_injective (N : ℕ) :
    Function.Injective (bakryBrownianFiniteDyadicEmbed N) := by
  intro i j h
  cases i with
  | none => cases j <;> simpa [bakryBrownianFiniteDyadicEmbed] using h
  | some i =>
    cases j with
    | none => simp [bakryBrownianFiniteDyadicEmbed] at h
    | some j =>
      cases i with
      | mk n k =>
        cases j with
        | mk m l =>
          have hnm : n.val = m.val := congrArg (fun x : BakryBrownianDyadicIndex =>
            match x with | none => 0 | some p => p.1) h
          have he : n = m := Fin.ext hnm
          cases he
          have hkl : k = l := by simpa [bakryBrownianFiniteDyadicEmbed] using h
          cases hkl
          rfl

/-- Genuine finite coefficient Gaussian law extracted from the internally
constructed countable independent Gaussian product. -/
theorem bakryBrownianFiniteDyadic_coordinates_gaussian (N : ℕ) :
    HasGaussianLaw (fun sample : BakryBrownianDyadicSample => fun i : BakryBrownianFiniteDyadicIndex N =>
      sample (bakryBrownianFiniteDyadicEmbed N i)) bakryBrownianDyadicMeasure := by
  apply iIndepFun.hasGaussianLaw
  · intro i
    exact (bakryBrownianDyadic_coordinate_law _).hasGaussianLaw
  · exact bakryBrownianDyadic_coordinates_independent.precomp (bakryBrownianFiniteDyadicEmbed_injective N)

/-- The literal finite Faber–Schauder evaluation is a concrete continuous
linear form of the finite product coefficients. -/
def bakryBrownianFiniteDyadicEvaluation (N : ℕ) (t : Icc (0 : ℝ) 1) :
    (BakryBrownianFiniteDyadicIndex N → ℝ) →L[ℝ] ℝ :=
  t.val • ContinuousLinearMap.proj none + ∑ n : Fin N, ∑ k : Fin (2^n.val),
    ((1/Real.sqrt 2)^n.val * bakryBrownianDyadicTent n.val k t) •
      ContinuousLinearMap.proj (some ⟨n,k⟩)

theorem bakryBrownianFiniteDyadicEvaluation_apply (N : ℕ) (t : Icc (0 : ℝ) 1)
    (x : BakryBrownianFiniteDyadicIndex N → ℝ) :
    bakryBrownianFiniteDyadicEvaluation N t x = x none*t.val +
      ∑ n : Fin N, (1/Real.sqrt 2)^n.val * ∑ k : Fin (2^n.val), x (some ⟨n,k⟩) *
        bakryBrownianDyadicTent n.val k t := by
  simp only [bakryBrownianFiniteDyadicEvaluation,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.sum_apply,smul_eq_mul]
  rw [mul_comm t.val]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Every finite vector of actual partial-series evaluations is jointly
Gaussian; shared coefficients are handled by one concrete linear map. -/
theorem bakryBrownianFiniteDyadic_evaluations_gaussian {ι : Type*} [Fintype ι]
    (N : ℕ) (t : ι → Icc (0 : ℝ) 1) :
    HasGaussianLaw (fun sample : BakryBrownianDyadicSample => fun a : ι =>
      sample none*(t a).val + ∑ n : Fin N, (1/Real.sqrt 2)^n.val *
        ∑ k : Fin (2^n.val), sample (some ⟨n.val,k⟩)*bakryBrownianDyadicTent n.val k (t a))
      bakryBrownianDyadicMeasure := by
  let L : (BakryBrownianFiniteDyadicIndex N → ℝ) →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun a => bakryBrownianFiniteDyadicEvaluation N (t a))
  have h := (bakryBrownianFiniteDyadic_coordinates_gaussian N).map_fun L
  convert h using 1
  funext sample a
  simp only [L,ContinuousLinearMap.pi_apply,bakryBrownianFiniteDyadicEvaluation_apply,
    bakryBrownianFiniteDyadicEmbed]

#print axioms bakryBrownianFiniteDyadicEmbed_injective
#print axioms bakryBrownianFiniteDyadic_coordinates_gaussian
#print axioms bakryBrownianFiniteDyadicEvaluation_apply
#print axioms bakryBrownianFiniteDyadic_evaluations_gaussian
end
end GinibrePoincare
