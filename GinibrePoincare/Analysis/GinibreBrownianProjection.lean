module

public import GinibrePoincare.Analysis.GinibreDrivenPathFactorization
public import GinibrePoincare.Analysis.GaussianProjectionIndependence
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

open scoped BigOperators ComplexConjugate NNReal
open MeasureTheory ProbabilityTheory
namespace GinibrePoincare
noncomputable section

/-- The same finite configuration equipped with its standard real Euclidean norm. -/
abbrev GinibreRealEuclidean (n : ℕ) := PiLp 2 (fun _ : Fin n => ℂ)

def ginibreCenterProjectionCLM (n : ℕ) : Configuration n →L[ℝ] Configuration n :=
  ContinuousLinearMap.pi fun _ => (n : ℝ)⁻¹ • coordinateSumCLM n

@[simp] theorem ginibreCenterProjectionCLM_apply (n : ℕ) (z : Configuration n) :
    ginibreCenterProjectionCLM n z = projectToCenterLine n z := by
  ext i
  simp [ginibreCenterProjectionCLM, projectToCenterLine, coordinateSumCLM_apply,
    div_eq_mul_inv, Complex.real_smul, mul_comm]

def ginibreConfigToEuclidean (n : ℕ) : Configuration n ≃L[ℝ] GinibreRealEuclidean n :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm

def ginibreCenterProjectionEuclidean (n : ℕ) :
    GinibreRealEuclidean n →L[ℝ] GinibreRealEuclidean n :=
  (ginibreConfigToEuclidean n).toContinuousLinearMap.comp
    ((ginibreCenterProjectionCLM n).comp (ginibreConfigToEuclidean n).symm.toContinuousLinearMap)

def ginibreRecenterProjectionEuclidean (n : ℕ) :
    GinibreRealEuclidean n →L[ℝ] GinibreRealEuclidean n :=
  (ginibreConfigToEuclidean n).toContinuousLinearMap.comp
    ((recenteredCLM n).comp (ginibreConfigToEuclidean n).symm.toContinuousLinearMap)

@[simp] theorem ginibreConfigToEuclidean_apply (n : ℕ) (z : Configuration n) :
    ginibreConfigToEuclidean n z = WithLp.toLp 2 z := rfl

@[simp] theorem ginibreCenterProjectionEuclidean_apply (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreCenterProjectionEuclidean n z =
      WithLp.toLp 2 (projectToCenterLine n (WithLp.ofLp z)) := by
  simp [ginibreCenterProjectionEuclidean, ginibreConfigToEuclidean,
    PiLp.coe_continuousLinearEquiv, ginibreCenterProjectionCLM_apply]

@[simp] theorem ginibreRecenterProjectionEuclidean_apply (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreRecenterProjectionEuclidean n z =
      WithLp.toLp 2 (recenteredConfiguration n (WithLp.ofLp z)) := by
  simp [ginibreRecenterProjectionEuclidean, ginibreConfigToEuclidean,
    PiLp.coe_continuousLinearEquiv, recenteredCLM_apply]


theorem ginibreCenterProjectionEuclidean_selfAdjoint (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ x (ginibreCenterProjectionEuclidean n y) =
      inner ℝ (ginibreCenterProjectionEuclidean n x) y := by
  simp [PiLp.inner_apply, ginibreCenterProjectionEuclidean_apply,
    Complex.inner, projectToCenterLine, coordinateSum]
  simp_rw [Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring


theorem ginibreRecenterProjectionEuclidean_eq_sub (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreRecenterProjectionEuclidean n z =
      z - ginibreCenterProjectionEuclidean n z := by
  ext i
  simp [ginibreRecenterProjectionEuclidean_apply, ginibreCenterProjectionEuclidean_apply,
    recenteredConfiguration, projectToOrthogonal, projectToCenterLine]

theorem ginibreRecenterProjectionEuclidean_selfAdjoint (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ x (ginibreRecenterProjectionEuclidean n y) =
      inner ℝ (ginibreRecenterProjectionEuclidean n x) y := by
  rw [ginibreRecenterProjectionEuclidean_eq_sub, ginibreRecenterProjectionEuclidean_eq_sub]
  simp only [inner_sub_right, inner_sub_left]
  rw [ginibreCenterProjectionEuclidean_selfAdjoint]

theorem ginibreCenterProjectionEuclidean_recenter_zero (n : ℕ)
    (z : GinibreRealEuclidean n) :
    ginibreCenterProjectionEuclidean n (ginibreRecenterProjectionEuclidean n z) = 0 := by
  rw [ginibreCenterProjectionEuclidean_apply, ginibreRecenterProjectionEuclidean_apply]
  have hs := coordinateSum_recentered n (WithLp.ofLp z)
  ext i
  simp [projectToCenterLine, hs]

theorem ginibreCenterRecenterEuclidean_orthogonal (n : ℕ)
    (x y : GinibreRealEuclidean n) :
    inner ℝ (ginibreCenterProjectionEuclidean n x)
      (ginibreRecenterProjectionEuclidean n y) = 0 := by
  rw [← ginibreCenterProjectionEuclidean_selfAdjoint n x
    (ginibreRecenterProjectionEuclidean n y)]
  rw [ginibreCenterProjectionEuclidean_recenter_zero n y]
  simp

/-- The actual Ginibre center and recentered projections preserve Brownian
paths and have the covariance of their respective orthogonal subspaces. -/
theorem ginibreBrownianNoise_projections_are_brownian
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {B : ℝ≥0 → Ω → GinibreRealEuclidean n}
    (hB : IsBrownianVectorProcess B μ) :
    IsProjectedBrownianVectorProcess
      (fun t ω => ginibreCenterProjectionEuclidean n (B t ω)) μ
        (ginibreCenterProjectionEuclidean n) ∧
    IsProjectedBrownianVectorProcess
      (fun t ω => ginibreRecenterProjectionEuclidean n (B t ω)) μ
        (ginibreRecenterProjectionEuclidean n) := by
  exact ⟨hB.project _ (ginibreCenterProjectionEuclidean_selfAdjoint n),
    hB.project _ (ginibreRecenterProjectionEuclidean_selfAdjoint n)⟩

/-- A standard Gaussian configuration noise splits into independent center and
recentered noise processes. This is the Brownian-independence assertion in the
paper, stated in the finite-dimensional Gaussian-process formulation. -/
theorem ginibreGaussianNoise_center_recenter_independent
    (n : ℕ) {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {B : ℝ≥0 → Ω → GinibreRealEuclidean n}
    (hB : IsBrownianVectorProcess B μ) :
    IndepFun (fun ω t => ginibreCenterProjectionEuclidean n (B t ω))
      (fun ω t => ginibreRecenterProjectionEuclidean n (B t ω)) μ := by
  apply orthogonalGaussianProjections_indepFun hB.toIsGaussianProcessWithBrownianCovariance
    (ginibreCenterProjectionEuclidean n) (ginibreRecenterProjectionEuclidean n)
  · exact ginibreCenterProjectionEuclidean_selfAdjoint n
  · exact ginibreRecenterProjectionEuclidean_selfAdjoint n
  · exact ginibreCenterRecenterEuclidean_orthogonal n

end
end GinibrePoincare
