module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicUniform
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianFinite
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianDyadicGaussianMoments
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def bakryBrownianDyadicWeights (N : ℕ) (t : Icc (0 : ℝ) 1) : BakryBrownianFiniteDyadicIndex N → ℝ
  | none => t.val
  | some ⟨n,k⟩ => (1/Real.sqrt 2)^n.val * bakryBrownianDyadicTent n.val k t

/-- Actual partial path equals its literal finite coefficient linear form. -/
theorem bakryBrownianDyadicPartialPath_finite (N : ℕ) (sample : BakryBrownianDyadicSample)
    (t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicPartialPath N sample t =
      sample none*t.val + ∑ n : Fin N, (1/Real.sqrt 2)^n.val *
        ∑ k : Fin (2^n.val), sample (some ⟨n.val,k⟩)*bakryBrownianDyadicTent n.val k t := by
  simp only [bakryBrownianDyadicPartialPath,bakryBrownianDyadicLevel,
    ContinuousMap.add_apply,ContinuousMap.smul_apply,ContinuousMap.sum_apply,
    bakryBrownianDyadicLinearPath,ContinuousMap.coe_mk,smul_eq_mul]
  congr 1
  exact (Fin.sum_univ_eq_sum_range (fun n : ℕ => (1/Real.sqrt 2)^n *
    ∑ k : Fin (2^n),sample (some ⟨n,k⟩)*bakryBrownianDyadicTent n k t) N).symm

/-- Genuine Gaussian finite-dimensional laws of the actual root partial
paths, with all shared level coefficients retained. -/
theorem bakryBrownianDyadicPartialPath_gaussian {ι : Type*} [Fintype ι]
    (N : ℕ) (t : ι → Icc (0 : ℝ) 1) :
    HasGaussianLaw (fun sample : BakryBrownianDyadicSample => fun a : ι =>
      bakryBrownianDyadicPartialPath N sample (t a)) bakryBrownianDyadicMeasure := by
  have h := bakryBrownianFiniteDyadic_evaluations_gaussian N t
  convert h using 1
  funext sample a
  exact bakryBrownianDyadicPartialPath_finite N sample (t a)

theorem bakryBrownianDyadicPartialPath_linear (N : ℕ) (sample : BakryBrownianDyadicSample)
    (t : Icc (0 : ℝ) 1) :
    bakryBrownianDyadicPartialPath N sample t =
      bakryBrownianFiniteDyadicLinear N (bakryBrownianDyadicWeights N t) sample := by
  rw [bakryBrownianDyadicPartialPath_finite]
  simp only [bakryBrownianFiniteDyadicLinear,Fintype.sum_option,Fintype.sum_sigma,
    bakryBrownianDyadicWeights,bakryBrownianFiniteDyadicEmbed]
  rw [mul_comm (t : ℝ)]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem bakryBrownianDyadicWeights_inner (N : ℕ) (s t : Icc (0 : ℝ) 1) :
    (∑ i, bakryBrownianDyadicWeights N s i * bakryBrownianDyadicWeights N t i) =
      (s : ℝ)*(t : ℝ)+∑ n ∈ Finset.range N, (1/2 : ℝ)^n *
        ∑ k : Fin (2^n), bakryBrownianDyadicTent n k s * bakryBrownianDyadicTent n k t := by
  have hq : (1/Real.sqrt 2)*(1/Real.sqrt 2) = (1/2 : ℝ) := by
    rw [← pow_two,div_pow,one_pow,Real.sq_sqrt (by norm_num)]
  have hpow (n : ℕ) : (1/Real.sqrt 2)^n*(1/Real.sqrt 2)^n = (1/2 : ℝ)^n := by
    rw [← mul_pow,hq]
  simp only [Fintype.sum_option,Fintype.sum_sigma,bakryBrownianDyadicWeights]
  congr 1
  calc
    _ = ∑ n : Fin N, (1/2 : ℝ)^n.val * ∑ k : Fin (2^n.val),
        bakryBrownianDyadicTent n.val k s * bakryBrownianDyadicTent n.val k t := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      calc
        _ = ((1/Real.sqrt 2)^n.val*(1/Real.sqrt 2)^n.val)*
          (bakryBrownianDyadicTent n.val k s * bakryBrownianDyadicTent n.val k t) := by ring
        _ = _ := by rw [hpow]
    _ = _ := Fin.sum_univ_eq_sum_range (fun n : ℕ => (1/2 : ℝ)^n *
      ∑ k : Fin (2^n), bakryBrownianDyadicTent n k s * bakryBrownianDyadicTent n k t) N

theorem bakryBrownianDyadicPartialPath_mean (N : ℕ) (t : Icc (0 : ℝ) 1) :
    (∫ sample, bakryBrownianDyadicPartialPath N sample t ∂bakryBrownianDyadicMeasure) = 0 := by
  simp_rw [bakryBrownianDyadicPartialPath_linear]
  exact bakryBrownianFiniteDyadicLinear_mean N _

theorem bakryBrownianDyadicPartialPath_covariance (N : ℕ) (s t : Icc (0 : ℝ) 1) :
    cov[(fun sample => bakryBrownianDyadicPartialPath N sample s),
      (fun sample => bakryBrownianDyadicPartialPath N sample t);bakryBrownianDyadicMeasure] =
      (s : ℝ)*(t : ℝ)+∑ n ∈ Finset.range N, (1/2 : ℝ)^n *
        ∑ k : Fin (2^n), bakryBrownianDyadicTent n k s * bakryBrownianDyadicTent n k t := by
  simp_rw [bakryBrownianDyadicPartialPath_linear]
  rw [bakryBrownianFiniteDyadicLinear_covariance,bakryBrownianDyadicWeights_inner]

def bakryBrownianDyadicLinearWeights {ι : Type*} [Fintype ι] (N : ℕ)
    (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) (i : BakryBrownianFiniteDyadicIndex N) : ℝ :=
  ∑ a, c a * bakryBrownianDyadicWeights N (t a) i

theorem bakryBrownianDyadicPartialPath_linear_combination {ι : Type*} [Fintype ι]
    (N : ℕ) (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) (sample : BakryBrownianDyadicSample) :
    (∑ a, c a * bakryBrownianDyadicPartialPath N sample (t a)) =
      bakryBrownianFiniteDyadicLinear N (bakryBrownianDyadicLinearWeights N t c) sample := by
  simp_rw [bakryBrownianDyadicPartialPath_linear]
  simp only [bakryBrownianFiniteDyadicLinear,bakryBrownianDyadicLinearWeights,
    Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem bakryBrownianDyadicLinearWeights_normSq {ι : Type*} [Fintype ι]
    (N : ℕ) (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) :
    (∑ i, (bakryBrownianDyadicLinearWeights N t c i)^2) =
      ∑ a, ∑ b, c a*c b*(∑ i,bakryBrownianDyadicWeights N (t a) i*bakryBrownianDyadicWeights N (t b) i) := by
  simp only [bakryBrownianDyadicLinearWeights,pow_two]
  simp_rw [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro i hi
  ring

def bakryBrownianDyadicQuadraticKernel {ι : Type*} [Fintype ι] (N : ℕ)
    (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) : ℝ :=
  ∑ a, ∑ b, c a*c b*((t a : ℝ)*(t b : ℝ)+∑ n ∈ Finset.range N, (1/2 : ℝ)^n *
    ∑ k : Fin (2^n),bakryBrownianDyadicTent n k (t a)*bakryBrownianDyadicTent n k (t b))

theorem bakryBrownianDyadicPartialPath_linear_law {ι : Type*} [Fintype ι]
    (N : ℕ) (t : ι → Icc (0 : ℝ) 1) (c : ι → ℝ) :
    HasLaw (fun sample : BakryBrownianDyadicSample =>
      ∑ a, c a*bakryBrownianDyadicPartialPath N sample (t a))
      (gaussianReal 0 (bakryBrownianDyadicQuadraticKernel N t c).toNNReal) bakryBrownianDyadicMeasure := by
  have h := bakryBrownianFiniteDyadicLinear_law N (bakryBrownianDyadicLinearWeights N t c)
  rw [bakryBrownianDyadicLinearWeights_normSq] at h
  simp_rw [bakryBrownianDyadicWeights_inner] at h
  convert h using 1
  · funext sample
    exact bakryBrownianDyadicPartialPath_linear_combination N t c sample
  · rfl

#print axioms bakryBrownianDyadicPartialPath_linear_combination
#print axioms bakryBrownianDyadicLinearWeights_normSq
#print axioms bakryBrownianDyadicPartialPath_linear_law
#print axioms bakryBrownianDyadicPartialPath_linear
#print axioms bakryBrownianDyadicWeights_inner
#print axioms bakryBrownianDyadicPartialPath_mean
#print axioms bakryBrownianDyadicPartialPath_covariance
#print axioms bakryBrownianDyadicPartialPath_finite
#print axioms bakryBrownianDyadicPartialPath_gaussian
end
end GinibrePoincare
