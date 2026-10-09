module

public import GinibrePoincare.Analysis.GinibreStochasticAugmentedQuadraticVariation
public import GinibrePoincare.Analysis.FiniteDimensionalItoDriftRiemann
public import GinibrePoincare.Analysis.FiniteDimensionalItoConvergenceInMeasure

@[expose] public section

/-! Actual adapted continuous weighted Brownian quadratic variation converges to its time integral. -/
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def ginibreBrownianAugmentedWeightedDiagonal {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (t : ℝ≥0) (A : ℝ≥0 → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ∑ i : Fin (n+1), A (ginibreUniformBrownianTime t n i) ω*
    (B (ginibreUniformBrownianTime t n (i.val+1)) ω-B (ginibreUniformBrownianTime t n i) ω)^2

theorem ginibreBrownianAugmentedWeightedDiagonal_tendstoInProbability {Ω ι : Type*}
    [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsPreBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (j : ι) (t : ℝ≥0) (A : ℝ≥0 → Ω → ℝ)
    (hA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P hB) A)
    (hc : ∀ᵐ ω ∂P, Continuous (fun s => A s ω))
    (C : ℝ) (hbound : ∀ s ω, ‖A s ω‖ ≤ C) :
    TendstoInMeasure P (ginibreBrownianAugmentedWeightedDiagonal (B j) t A) atTop
      (fun ω => ∫ s in (0 : ℝ)..t, A s.toNNReal ω) := by
  let F := fun (n : ℕ) (i : Fin (n+1)) => A (ginibreUniformBrownianTime t n i)
  have hF (n : ℕ) (i : Fin (n+1)) : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P hB (ginibreUniformBrownianTime t n i)) _ (F n i) := (hA _).measurable
  let E := fun n => ginibreBrownianAugmentedQuadraticError (B j) t n (F n)
  have hE := ginibreBrownianAugmentedQuadraticError_tendstoInProbability B P hB hind j t F hF C
    (fun n i ω => hbound _ ω)
  have hEm (n : ℕ) : AEStronglyMeasurable (E n) P :=
    (ginibreBrownianAugmentedQuadraticError_memLp_two B P hB hind j t n (F n) (hF n) C
      (fun i ω => hbound _ ω)).aestronglyMeasurable
  let R := fun (n : ℕ) (ω : Ω) => ∑ i : Fin (n+1), F n i ω*((t : ℝ)/((n : ℝ)+1))
  have hRm (n : ℕ) : AEStronglyMeasurable (R n) P := by
    have hEach (i : Fin (n+1)) : AEStronglyMeasurable (fun ω => F n i ω*((t : ℝ)/((n : ℝ)+1))) P :=
      ((hA _).mono ((ginibreBrownianAugmentedFiltration B P hB).le _)).aestronglyMeasurable.mul_const _
    convert! Finset.aestronglyMeasurable_sum Finset.univ (fun i _ => hEach i) using 1
    ext ω
    simp [R]
  have hR : TendstoInMeasure P R atTop (fun ω => ∫ s in (0 : ℝ)..t, A s.toNNReal ω) := by
    apply tendstoInMeasure_of_tendsto_ae hRm
    filter_upwards [hc] with ω hω
    have h := itoContinuousScalarRiemann_fin_tendsto (fun s : ℝ => A s.toNNReal ω) t
      (hω.comp continuous_real_toNNReal).continuousOn
    simpa only [Real.toNNReal_coe] using h
  have hSum := itoTendstoInMeasure_add P E R (fun _ => 0) _ hEm hRm hE hR
  apply TendstoInMeasure.congr _ (Eventually.of_forall (fun ω => zero_add _)) hSum
  intro n
  apply Eventually.of_forall
  intro ω
  dsimp only [E, R, F, ginibreBrownianAugmentedQuadraticError, ginibreBrownianAugmentedWeightedDiagonal]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

end
end GinibrePoincare
