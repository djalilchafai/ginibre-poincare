module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOURiemann
public import GinibrePoincare.Analysis.GinibreStochasticOUPast
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.Order.LiminfLimsup

@[expose] public section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownianOU_zero_isGaussianProcess {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (rate : ℝ≥0) :
    IsGaussianProcess (fun (t : ℝ≥0) ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t ω) P := by
  classical
  constructor
  intro I
  let e := PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)
  let X (m : ℕ) (ω : Ω) : EuclideanSpace ℝ I :=
    WithLp.toLp 2 (fun i => ginibreBrownianOURiemannSum B rate i.val m ω)
  let Y (ω : Ω) : EuclideanSpace ℝ I :=
    WithLp.toLp 2 (fun i => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 i.val ω)
  have hG (m : ℕ) : HasGaussianLaw (X m) P :=
    ((ginibreBrownianOURiemann_isGaussianProcess B P hB.toIsPreBrownianReal rate m).hasGaussianLaw I).map e.symm.toContinuousLinearMap
  have hm (m : ℕ) : (∫ ω, X m ω ∂P)=0 := by
    ext i
    have h := (PiLp.proj 2 (fun _ : I => ℝ) i : EuclideanSpace ℝ I →L[ℝ] ℝ).integral_comp_comm (hG m).integrable
    have hL := ginibreBrownianOURiemannSum_hasLaw B P hB.toIsPreBrownianReal rate i.val m
    simpa [X,PiLp.proj_apply,hL.integral_eq] using h.symm
  have hb (i : I) : ∃ C : ℝ≥0, ∀ m, ginibreBrownianOURiemannVariance rate i.val m ≤ C := by
    obtain ⟨C,hC⟩ := (ginibreBrownianOURiemannVariance_tendsto rate i.val).bddAbove_range
    exact ⟨C,fun m => hC (mem_range_self m)⟩
  choose C hC using hb
  have hbound (m : ℕ) : (∫ ω, ‖X m ω‖^2 ∂P) ≤ ∑ i : I, (C i : ℝ) := by
    simp_rw [PiLp.norm_sq_eq_of_L2, X, Real.norm_eq_abs, sq_abs]
    rw [integral_finset_sum _ (fun i _ =>
      (ginibreBrownianOURiemannSum_hasLaw B P hB.toIsPreBrownianReal rate i.val m).hasGaussianLaw.memLp_two.integrable_sq)]
    simp_rw [ginibreBrownianOURiemann_second_moment B P hB.toIsPreBrownianReal]
    exact Finset.sum_le_sum (fun i _ => NNReal.coe_le_coe.mpr (hC i m))
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun m => X m ω) atTop (𝓝 (Y ω)) := by
    filter_upwards [ae_all_iff.mpr (fun i : I =>
      ginibreBrownianOURiemannSum_ae_tendsto B P hB rate i.val)] with ω hω
    exact (PiLp.continuous_toLp 2 _).continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hω)
  have hY := centeredGaussian_vector_ae_limit_hasGaussianLaw_of_second_moment_bound
    P X Y hG hm (∑ i : I, (C i : ℝ)) hbound hlim
  exact hY.map e.toContinuousLinearMap

theorem independent_gaussian_initial_process_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Ω → ℝ) (X : ℝ≥0 → Ω → ℝ) (hZ : HasGaussianLaw Z P)
    (hX : IsGaussianProcess X P)
    (hind : IndepFun Z (fun ω t => X t ω) P) (a : ℝ≥0 → ℝ) :
    IsGaussianProcess (fun t ω => a t * Z ω + X t ω) P := by
  classical
  constructor
  intro I
  let Y : Ω → I → ℝ := fun ω i => X i.val ω
  have hY : HasGaussianLaw Y P := hX.hasGaussianLaw I
  have hr : Measurable (fun p : ℝ≥0 → ℝ => fun i : I => p i.val) :=
    Measurable.of_eval (fun i => measurable_pi_apply i.val)
  have hI : IndepFun Z Y P := hind.comp measurable_id hr
  have hpair : HasGaussianLaw (fun ω => (Z ω,Y ω)) P := by
    constructor
    · exact hZ.aemeasurable.prodMk hY.aemeasurable
    · rw [hI.map_prod_eq_prod_map_map hZ.aemeasurable hY.aemeasurable]
      letI := hZ.isGaussian_map
      letI := hY.isGaussian_map
      infer_instance
  let L : (ℝ × (I → ℝ)) →L[ℝ] (I → ℝ) :=
    { toFun := fun p i => a i.val * p.1 + p.2 i
      map_add' := by intro x y; ext i; simp; ring
      map_smul' := by intro c x; ext i; simp; ring }
  exact hpair.map L

theorem ginibreBrownianOU_gaussian_initial_isGaussianProcess
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (hB : IsBrownianReal B P)
    (Z : Ω → ℝ) (hZ : HasGaussianLaw Z P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate : ℝ≥0) :
    IsGaussianProcess (fun (t : ℝ≥0) ω =>
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t ω) P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω =>
    ginibreOUConvolutionFunctional rate t (fun s => B s ω)
  have heq (t : ℝ≥0) : X t =ᵐ[P]
      ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t :=
    ginibreOUConvolutionFunctional_ae_eq B P hB rate t
  have hX : IsGaussianProcess X P :=
    (ginibreBrownianOU_zero_isGaussianProcess B P hB rate).congr (fun t => (heq t).symm)
  have hr : Measurable (fun p : ℝ≥0 → ℝ => fun t : ℝ≥0 => ginibreOUConvolutionFunctional rate t p) :=
    Measurable.of_eval (fun t => ginibreOUConvolutionFunctional_measurable rate t)
  have hI : IndepFun Z (fun ω t => X t ω) P := hind.comp measurable_id hr
  apply (independent_gaussian_initial_process_isGaussianProcess P Z X hZ hX hI
    (ginibreOUDecay rate)).congr
  intro t
  filter_upwards [heq t] with ω hω
  rw [hω]
  change ginibreOUDecay rate t * Z ω + drivenOUPath rate 0
    (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t =
      drivenOUPath rate (Z ω) (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t
  conv_rhs => rw [drivenOUPath_initial_split]
  rfl

end
end GinibrePoincare
