module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralPuncturedPartialContinuous
public import GinibrePoincare.Analysis.GinibreBrownianIntegralSubstitution
public import GinibrePoincare.Analysis.GinibreStochasticUnitFieldPartialMeanSquare

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000

theorem brownianAggregateUniformSum_punctured_meanSquare_of_horizon_limit
    {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (hind : iIndepFun (fun i ω t => B i t ω) P)
    (F : ι → ℝ≥0 → Ω → ℝ)
    (hF : ∀ i r, @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) r) _ (F i r))
    (T : ℝ≥0) (hT : 0 < T) (hc : ∀ i, ∀ᵐ ω ∂P, ContinuousOn (fun r => F i r ω) (Set.Ioi 0))
    (C : ℝ) (hC : 0≤C) (hb : ∀ i r ω, ‖F i r ω‖≤C)
    (J : Ω → ℝ)
    (hlim : TendstoInMeasure P (fun k ω => ∑ i, brownianUniformLeftSum (B i) (F i) T (k+1) ω)
      atTop J) :
    MemLp J 2 P ∧ Tendsto (fun k => ∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (F i) T (k+1) ω)-J ω)^2 ∂P) atTop (𝓝 0) := by
  classical
  have hex (i : ι) := brownianPuncturedPartialIntegral_exists B P hB hind i (F i) (hF i)
    (hc i) C hC (hb i) T hT
  choose M hM hMC hML hM0 hMS using hex
  have hi (i : ι) : TendstoInMeasure P
      (fun k => brownianUniformLeftSum (B i) (F i) T (k+1)) atTop (M i T) := by
    have he : (fun k => brownianUniformPartialSum (B i) (F i) T (k+1) T) =
        (fun k => brownianUniformLeftSum (B i) (F i) T (k+1)) := by
      funext k ω
      exact brownianUniformPartialSum_terminal (B i) (F i) T (k+1) ω
    rw [← he]
    apply ginibre_tendstoInMeasure_of_meanSquare P _ _
    · intro k
      exact ((brownianUniformPartialSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal)
        hind i (F i) (hF i) (fun r => MemLp.of_bound
          (((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
            (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable)
          C (ae_of_all P (hb i r))) T (k+1) T).sub (hML i T)).integrable_sq
    · exact hMS i T le_rfl
  have hFi (i : ι) (r : ℝ≥0) : MemLp (F i r) 2 P := MemLp.of_bound
    (((hF i r).mono ((ginibreBrownianAugmentedFiltration B P
      (fun i => (hB i).toIsPreBrownianReal)).le r) le_rfl).aestronglyMeasurable)
    C (Eventually.of_forall (hb i r))
  have hSL (i : ι) (k : ℕ) : MemLp (brownianUniformLeftSum (B i) (F i) T (k+1)) 2 P :=
    brownianUniformLeftSum_memLp_two B P (fun i => (hB i).toIsPreBrownianReal) hind
      i (F i) (hF i) (hFi i) T (k+1)
  have hsum := itoTendstoInMeasure_finset_sum P Finset.univ
    (fun i k => brownianUniformLeftSum (B i) (F i) T (k+1)) (fun i => M i T)
    (fun i k => (hSL i k).aestronglyMeasurable) hi
  have he := tendstoInMeasure_ae_unique hsum hlim
  have hJL : MemLp (fun ω => ∑ i, M i T ω) 2 P := memLp_finsetSum _ (fun i hi => hML i T)
  refine ⟨hJL.ae_eq he,?_⟩
  have hh := actualMeanSquareZero_finset_sum P Finset.univ
    (fun i k ω => brownianUniformLeftSum (B i) (F i) T (k+1) ω-M i T ω)
    (fun i k => (hSL i k).sub (hML i T))
    (fun i => by simpa only [brownianUniformPartialSum_terminal] using hMS i T le_rfl)
  have hEq (k : ℕ) : (∫ ω,
      ((∑ i, brownianUniformLeftSum (B i) (F i) T (k+1) ω)-J ω)^2 ∂P) =
      ∫ ω, (∑ i, (brownianUniformLeftSum (B i) (F i) T (k+1) ω-M i T ω))^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [← hω, Finset.sum_sub_distrib]
  simp_rw [hEq]
  exact hh

#print axioms brownianAggregateUniformSum_punctured_meanSquare_of_horizon_limit
end
end GinibrePoincare
