module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobalPath
public import Mathlib.Probability.Moments.Covariance
@[expose] public section
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
local instance bakryGlobalCovariance_pathMeasurable : MeasurableSpace C(Icc (0 : ℝ) 1, ℝ) := borel _
local instance bakryGlobalCovariance_pathBorel : BorelSpace C(Icc (0 : ℝ) 1, ℝ) := ⟨rfl⟩

theorem bakryBrownianGlobalProcess_covariance_of_unit
    (hL : ∀ t : Icc (0 : ℝ) 1, MemLp (fun ω => bakryBrownianDyadicCompletedPath ω t) 2
      bakryBrownianDyadicCompletedMeasure)
    (hC : ∀ s t : Icc (0 : ℝ) 1, cov[fun ω => bakryBrownianDyadicCompletedPath ω s,
      fun ω => bakryBrownianDyadicCompletedPath ω t;bakryBrownianDyadicCompletedMeasure] = min (s : ℝ) (t : ℝ))
    (s t : ℝ≥0) : cov[bakryBrownianGlobalProcess s, bakryBrownianGlobalProcess t;
      bakryBrownianGlobalMeasure] = min (s : ℝ) (t : ℝ) := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((s : ℝ)+(t : ℝ))
  have hsN : (s : ℝ) ≤ N := by linarith [t.coe_nonneg]
  have htN : (t : ℝ) ≤ N := by linarith [s.coe_nonneg]
  let F (r : ℝ≥0) (n : ℕ) (ω : BakryBrownianDyadicCompletedSample) : ℝ :=
    bakryBrownianDyadicCompletedPath ω (bakryBrownianUnitClamp ((r : ℝ)-n))
  have hF (r : ℝ≥0) (n : ℕ) : Measurable (F r n) :=
    (continuous_eval_const _).measurable.comp bakryBrownianDyadicCompletedPath_measurable
  have hFL (r : ℝ≥0) (n : ℕ) : MemLp (fun ω : BakryBrownianGlobalSample => F r n (ω n)) 2
      bakryBrownianGlobalMeasure := by
    exact (hL _).comp_measurePreserving
      (measurePreserving_eval_infinitePi (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure) n)
  have he (r : ℝ≥0) (hr : (r : ℝ) ≤ N) : bakryBrownianGlobalProcess r =
      fun ω => ∑ n ∈ Finset.range N, F r n (ω n) := by
    funext ω
    exact bakryBrownianGlobalPath_eq_finite ω N r hr
  rw [he s hsN, he t htN, covariance_fun_sum_fun_sum' (fun n _ => hFL s n) (fun n _ => hFL t n)]
  have hdiag (n : ℕ) : cov[fun ω : BakryBrownianGlobalSample => F s n (ω n),
      fun ω => F t n (ω n);bakryBrownianGlobalMeasure] =
      min (bakryBrownianUnitClamp ((s : ℝ)-n) : ℝ) (bakryBrownianUnitClamp ((t : ℝ)-n) : ℝ) := by
    have hp := measurePreserving_eval_infinitePi (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure) n
    rw [← covariance_map_fun ((hF s n).aestronglyMeasurable) ((hF t n).aestronglyMeasurable)
      hp.measurable.aemeasurable]
    change cov[F s n, F t n;(Measure.infinitePi (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure)).map (Function.eval n)] = _
    rw [hp.map_eq]
    exact hC _ _
  have hoff (n m : ℕ) (hnm : n ≠ m) : cov[fun ω : BakryBrownianGlobalSample => F s n (ω n),
      fun ω => F t m (ω m);bakryBrownianGlobalMeasure] = 0 := by
    have hij := (iIndepFun_infinitePi (P := fun _ : ℕ => bakryBrownianDyadicCompletedMeasure) (fun _ : ℕ =>
      (measurable_id : Measurable (id : BakryBrownianDyadicCompletedSample → BakryBrownianDyadicCompletedSample)))).indepFun hnm
    exact (hij.comp (hF s n) (hF t m)).covariance_eq_zero (hFL s n) (hFL t m)
  calc
    _ = ∑ n ∈ Finset.range N, min (bakryBrownianUnitClamp ((s : ℝ)-n) : ℝ)
        (bakryBrownianUnitClamp ((t : ℝ)-n) : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.sum_eq_single n]
      · exact hdiag n
      · intro m hm hmn
        exact hoff n m hmn.symm
      · exact fun hn' => (hn' hn).elim
    _ = _ := bakryBrownianUnitClamp_sum_min N s t s.coe_nonneg t.coe_nonneg hsN htN

theorem bakryBrownianGlobalProcess_mean_of_unit
    (hL : ∀ t : Icc (0 : ℝ) 1, MemLp (fun ω => bakryBrownianDyadicCompletedPath ω t) 2
      bakryBrownianDyadicCompletedMeasure)
    (hM : ∀ t : Icc (0 : ℝ) 1, (∫ ω, bakryBrownianDyadicCompletedPath ω t
      ∂bakryBrownianDyadicCompletedMeasure) = 0) (t : ℝ≥0) :
    (∫ ω, bakryBrownianGlobalProcess t ω ∂bakryBrownianGlobalMeasure) = 0 := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  let F (n : ℕ) (ω : BakryBrownianDyadicCompletedSample) : ℝ :=
    bakryBrownianDyadicCompletedPath ω (bakryBrownianUnitClamp ((t : ℝ)-n))
  have hF (n : ℕ) : Measurable (F n) :=
    (continuous_eval_const _).measurable.comp bakryBrownianDyadicCompletedPath_measurable
  have hp (n : ℕ) := measurePreserving_eval_infinitePi
    (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure) n
  have hFL (n : ℕ) : MemLp (fun ω : BakryBrownianGlobalSample => F n (ω n)) 2
      bakryBrownianGlobalMeasure := (hL _).comp_measurePreserving (hp n)
  have hm (n : ℕ) : (∫ ω : BakryBrownianGlobalSample, F n (ω n)
      ∂bakryBrownianGlobalMeasure) = 0 := by
    rw [← integral_map (hp n).measurable.aemeasurable (hF n).aestronglyMeasurable]
    change (∫ ω, F n ω ∂(Measure.infinitePi (fun _ : ℕ =>
      bakryBrownianDyadicCompletedMeasure)).map (Function.eval n)) = 0
    rw [(hp n).map_eq]
    exact hM _
  have he : bakryBrownianGlobalProcess t = fun ω => ∑ n ∈ Finset.range N, F n (ω n) := by
    funext ω
    exact bakryBrownianGlobalPath_eq_finite ω N t hN.le
  rw [he, integral_finsetSum (Finset.range N) (fun n hn => (hFL n).integrable (by norm_num))]
  simp only [hm, Finset.sum_const_zero]

theorem bakryBrownianGlobalProcess_memLp_of_unit
    (hL : ∀ t : Icc (0 : ℝ) 1, MemLp (fun ω => bakryBrownianDyadicCompletedPath ω t) 2
      bakryBrownianDyadicCompletedMeasure) (t : ℝ≥0) :
    MemLp (bakryBrownianGlobalProcess t) 2 bakryBrownianGlobalMeasure := by
  obtain ⟨N, hN⟩ := exists_nat_gt (t : ℝ)
  have he : bakryBrownianGlobalProcess t = fun ω => ∑ n ∈ Finset.range N,
      bakryBrownianDyadicCompletedPath (ω n) (bakryBrownianUnitClamp ((t : ℝ)-n)) := by
    funext ω
    exact bakryBrownianGlobalPath_eq_finite ω N t hN.le
  rw [he]
  apply memLp_finsetSum
  intro n hn
  exact (hL _).comp_measurePreserving (measurePreserving_eval_infinitePi
    (fun _ : ℕ => bakryBrownianDyadicCompletedMeasure) n)

theorem bakryBrownianDyadicCompleted_forget_measurePreserving :
    @MeasurePreserving BakryBrownianDyadicCompletedSample BakryBrownianDyadicSample
      (inferInstance : MeasurableSpace BakryBrownianDyadicCompletedSample) MeasurableSpace.pi
      (fun ω => ω) bakryBrownianDyadicCompletedMeasure bakryBrownianDyadicMeasure := by
  have hi : AEMeasurable (id : BakryBrownianDyadicSample → BakryBrownianDyadicSample)
      bakryBrownianDyadicMeasure := measurable_id.aemeasurable
  exact ⟨hi.nullMeasurable.measurable', bakryBrownianDyadic_completed_map id hi |>.trans Measure.map_id⟩

theorem bakryBrownianDyadicCompletedPath_memLp_of_original
    (hL : ∀ t : Icc (0 : ℝ) 1, MemLp (fun ω => bakryBrownianDyadicPath ω t) 2 bakryBrownianDyadicMeasure)
    (t : Icc (0 : ℝ) 1) : MemLp (fun ω => bakryBrownianDyadicCompletedPath ω t) 2
      bakryBrownianDyadicCompletedMeasure :=
  (hL t).comp_measurePreserving bakryBrownianDyadicCompleted_forget_measurePreserving

theorem bakryBrownianDyadicCompletedPath_mean_of_original
    (hM : ∀ t : Icc (0 : ℝ) 1, (∫ ω, bakryBrownianDyadicPath ω t ∂bakryBrownianDyadicMeasure) = 0)
    (t : Icc (0 : ℝ) 1) : (∫ ω, bakryBrownianDyadicCompletedPath ω t
      ∂bakryBrownianDyadicCompletedMeasure) = 0 := by
  have hf := (continuous_eval_const t).measurable.aemeasurable.comp_aemeasurable
    bakryBrownianDyadicPath_aemeasurable
  have hp := bakryBrownianDyadicCompleted_forget_measurePreserving
  change (∫ ω, (fun x => bakryBrownianDyadicPath x t) (ω : BakryBrownianDyadicSample)
    ∂bakryBrownianDyadicCompletedMeasure) = 0
  rw [← integral_map hp.measurable.aemeasurable (by rw [hp.map_eq];exact hf.aestronglyMeasurable), hp.map_eq]
  exact hM t

theorem bakryBrownianDyadicCompletedPath_covariance_of_original
    (hC : ∀ s t : Icc (0 : ℝ) 1, cov[fun ω => bakryBrownianDyadicPath ω s,
      fun ω => bakryBrownianDyadicPath ω t;bakryBrownianDyadicMeasure] = min (s : ℝ) (t : ℝ))
    (s t : Icc (0 : ℝ) 1) : cov[fun ω => bakryBrownianDyadicCompletedPath ω s,
      fun ω => bakryBrownianDyadicCompletedPath ω t;bakryBrownianDyadicCompletedMeasure] = min (s : ℝ) (t : ℝ) := by
  have hf (r : Icc (0 : ℝ) 1) := (continuous_eval_const r).measurable.aemeasurable.comp_aemeasurable
    bakryBrownianDyadicPath_aemeasurable
  have hp := bakryBrownianDyadicCompleted_forget_measurePreserving
  change cov[(fun x => bakryBrownianDyadicPath x s) ∘ (fun ω : BakryBrownianDyadicCompletedSample =>
    (ω : BakryBrownianDyadicSample)), (fun x => bakryBrownianDyadicPath x t) ∘
      (fun ω : BakryBrownianDyadicCompletedSample => (ω : BakryBrownianDyadicSample));
      bakryBrownianDyadicCompletedMeasure] = _
  rw [← covariance_map (by rw [hp.map_eq];exact (hf s).aestronglyMeasurable)
    (by rw [hp.map_eq];exact (hf t).aestronglyMeasurable) hp.measurable.aemeasurable, hp.map_eq]
  exact hC s t

#print axioms bakryBrownianGlobalProcess_covariance_of_unit
#print axioms bakryBrownianGlobalProcess_mean_of_unit
#print axioms bakryBrownianGlobalProcess_memLp_of_unit
#print axioms bakryBrownianDyadicCompleted_forget_measurePreserving
#print axioms bakryBrownianDyadicCompletedPath_memLp_of_original
#print axioms bakryBrownianDyadicCompletedPath_mean_of_original
#print axioms bakryBrownianDyadicCompletedPath_covariance_of_original
end
end GinibrePoincare
