module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOULimit
public import GinibrePoincare.Analysis.GinibreStochasticOUConvolution
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem ginibreBrownianOURiemann_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate : ℝ≥0) (m : ℕ) :
    IsGaussianProcess (fun t ω => ginibreBrownianOURiemannSum B rate t m ω) P := by
  classical
  apply hB.isGaussianProcess.of_isGaussianProcess
  intro t
  let I : Finset ℝ≥0 :=
    (Finset.univ.image (fun i : Fin (m+1) => ginibreUniformBrownianTime t m (i.val+1))) ∪
      (Finset.univ.image (fun i : Fin (m+1) => ginibreUniformBrownianTime t m i.val))
  have hS (i : Fin (m+1)) : ginibreUniformBrownianTime t m (i.val+1) ∈ I :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  have hP (i : Fin (m+1)) : ginibreUniformBrownianTime t m i.val ∈ I :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
  let L : (I → ℝ) →L[ℝ] ℝ :=
    ∑ i : Fin (m+1), ginibreOUStochasticWeight rate t (ginibreUniformTime t m i) •
      (ContinuousLinearMap.proj ⟨_,hS i⟩-ContinuousLinearMap.proj ⟨_,hP i⟩)
  refine ⟨I,L,?_⟩
  intro ω
  simp [L,ginibreBrownianOURiemannSum,Finset.restrict_def,smul_eq_mul]

theorem ginibreBrownianOURiemann_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsPreBrownianReal B P)
    (rate t : ℝ≥0) (m : ℕ) :
    (∫ ω, (ginibreBrownianOURiemannSum B rate t m ω)^2 ∂P) =
      (ginibreBrownianOURiemannVariance rate t m : ℝ) := by
  have hL := ginibreBrownianOURiemannSum_hasLaw B P hB rate t m
  have hmean : (∫ ω, ginibreBrownianOURiemannSum B rate t m ω ∂P)=0 := by
    simpa using hL.integral_eq
  have hv : variance (ginibreBrownianOURiemannSum B rate t m) P =
      (ginibreBrownianOURiemannVariance rate t m : ℝ) := by
    simpa [id_def] using hL.variance_eq
  rw [variance_eq_integral hL.aemeasurable, hmean] at hv
  simpa using hv

end
end GinibrePoincare
