module
public import GinibrePoincare.Analysis.CorrespondenceOperatorLocalMartingaleProblem
public import GinibrePoincare.Analysis.GinibreStochasticCompactTestDynkin
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable
@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
/-- Literal test-function martingale-problem deficit for the actual original diffusion. -/
def correspondenceOperator_test_deficit {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n×Fin 2)→ℝ≥0→Ω→ℝ)
    (f : Configuration n→ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  f (ginibreBrownianMaximalProcess n α z B t ω)-f z-
    ∫ s in (0:ℝ)..t,ginibreRealPaperSpeedGenerator n α f
      (ginibreBrownianMaximalProcess n α z B s.toNNReal ω)

/-- The actual Hamiltonian localization yields a sequence of true martingales,
uniformly bounded on each fixed horizon, converging to the literal deficit. -/
theorem correspondenceOperator_martingale_approximation
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0<n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n×Fin 2)→ℝ≥0→Ω→ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀i,IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P)
    (f : Configuration n→ℝ) (hf : IsGinibreCollisionFreeCompactTest f) (T : ℝ≥0) :
    ∃ M : ℕ→ℝ≥0→Ω→ℝ, ∃ C : ℝ,
      (∀m,Martingale (M m) (ginibreBrownianAugmentedFiltration B P
        (fun i => (hB i).toIsPreBrownianReal)) P) ∧
      (∀m,∀r≤T,∀ᵐ ω ∂P,‖M m r ω‖≤C) ∧
      (∀r≤T,∀ᵐ ω ∂P,Tendsto (fun m => M m r ω) atTop
        (𝓝 (correspondenceOperator_test_deficit n α z B f r ω))) := by
  classical
  let R : ℕ→ℝ := fun m => ginibreHamiltonian n z+m
  have hR (m : ℕ) : ginibreHamiltonian n z≤R m := by dsimp [R]; linarith [Nat.cast_nonneg (α := ℝ) m]
  let σ := fun m => ginibreBrownianHamiltonianBoundedStop n α z B (R m) T
  let X := fun m => ginibreBrownianHamiltonianStoppedProcess n α z B (R m) T
  have hf2 : ContDiffOn ℝ 2 f {x | CollisionFree x} :=
    (hf.1.of_le (WithTop.coe_le_coe.mpr (show (2:ENat)≤⊤ from le_top))).contDiffOn
  choose M hM hc hrepr using (fun m => correspondenceOperator_local_martingale_problem
    hn α z hz B P hB hind (R m) (hR m) T f hf2)
  obtain ⟨C,hC⟩ := hf.2.1.exists_bound_of_continuous hf.1.continuous
  have hLf : Continuous (ginibreRealPaperSpeedGenerator n α f) :=
    (continuous_ginibrePregenerator_of_compact_test hf).const_mul _
  have hLc : HasCompactSupport (ginibreRealPaperSpeedGenerator n α f) := by
    change HasCompactSupport ((fun _ => (α:ℝ)/(n:ℝ))*ginibrePregenerator n f)
    exact (hasCompactSupport_ginibrePregenerator hf.2.1).mul_left
  obtain ⟨D,hD⟩ := hLc.exists_bound_of_continuous hLf
  have hD0 : 0≤D := (norm_nonneg _).trans (hD z)
  refine ⟨M,C+‖f z‖+D*(T:ℝ),hM,?_,?_⟩
  · intro m r hr
    filter_upwards [hrepr m] with ω hω
    rw [← hω r]
    have hb : ‖∫ s in (0:ℝ)..(min (σ m ω) r:ℝ),
        ginibreRealPaperSpeedGenerator n α f (X m s.toNNReal ω)‖≤D*(T:ℝ) := by
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (0:ℝ)) (b := (min (σ m ω) r:ℝ))
        (fun s _ => hD (X m s.toNNReal ω))
      have hmin : (min (σ m ω) r:ℝ)≤T := (min_le_right _ _).trans hr
      exact hh.trans (by
        simpa only [sub_zero,abs_of_nonneg (show 0≤(min (σ m ω) r:ℝ) from (min (σ m ω) r).property)] using
          mul_le_mul_of_nonneg_left hmin hD0)
    have hn1 := norm_sub_le (f (X m r ω)) (f z)
    have hn2 := norm_sub_le (f (X m r ω)-f z)
      (∫ s in (0:ℝ)..(min (σ m ω) r:ℝ),ginibreRealPaperSpeedGenerator n α f (X m s.toNNReal ω))
    exact hn2.trans (add_le_add (hn1.trans (add_le_add (hC (X m r ω)) le_rfl)) hb)
  · intro r hr
    have hσlim : ∀ᵐ ω ∂P, ∀ᶠ m in atTop,σ m ω=T := by
      filter_upwards [ginibreBrownianMaximalLifetime_top_ae hn α z hz B P hB hind] with ω hω
      obtain ⟨c,hc⟩ := ginibreDrivenHamiltonianBoundedStop_eventually_eq_cap hn α
        (ginibreBrownianFullContinuousNoise n B α ω) z hz hω T
      have hRL : Tendsto R atTop atTop := tendsto_const_nhds.add_atTop tendsto_natCast_atTop_atTop
      filter_upwards [hRL.eventually (eventually_gt_atTop c)] with m hm
      exact (hc (R m) hm).2
    filter_upwards [hσlim,ae_all_iff.mpr hrepr] with ω hσω hrepω
    apply tendsto_const_nhds.congr'
    filter_upwards [hσω] with m hm
    rw [← hrepω m r]
    symm
    change f (X m r ω)-f z-(∫ s in (0:ℝ)..(min (σ m ω) r:ℝ),
      ginibreRealPaperSpeedGenerator n α f (X m s.toNNReal ω))=_
    rw [hm,min_eq_right (show (r:ℝ)≤T from hr)]
    have hXr : X m r ω=ginibreBrownianMaximalProcess n α z B r ω := by
      simp only [X,ginibreBrownianHamiltonianStoppedProcess,show
        ginibreBrownianHamiltonianBoundedStop n α z B (R m) T ω=T from hm,min_eq_left hr]
    rw [hXr]
    unfold correspondenceOperator_test_deficit
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le (show (0:ℝ)≤r from r.property)] at hs
    have hsT : s.toNNReal≤T := (Real.toNNReal_le_iff_le_coe).mpr (hs.2.trans hr)
    simp only [X,ginibreBrownianHamiltonianStoppedProcess,show
      ginibreBrownianHamiltonianBoundedStop n α z B (R m) T ω=T from hm,min_eq_left hsT]
#print axioms correspondenceOperator_martingale_approximation
end
end GinibrePoincare
