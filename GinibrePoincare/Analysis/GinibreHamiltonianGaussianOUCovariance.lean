module

public import GinibrePoincare.Analysis.GinibreHamiltonianGaussianOUProcess
public import GinibrePoincare.Analysis.GinibreStochasticOUJointLaw
public import Mathlib.Probability.Moments.Variance

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ginibreBrownianOU_zero_covariance_step {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (rate s t : ℝ≥0) :
    covariance (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 s)
      (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 (s+t)) P =
      ginibreOUDecay rate t * (ginibreOUVariance rate s : ℝ) := by
  let X := ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 s
  let Y := ginibreBrownianOUInnovation B rate s t
  letI : IsGaussian (ginibreOUTransition rate s 0) := by
    change IsGaussian (gaussianReal _ _)
    infer_instance
  have hX := (ginibreBrownianOU_zero_hasLaw B P hB rate s).hasGaussianLaw.memLp_two
  have hY := (ginibreBrownianOUInnovation_hasLaw B P hB rate s t).hasGaussianLaw.memLp_two
  have he : ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 (s+t) =ᵐ[P]
      (fun ω => ginibreOUDecay rate t * X ω + Y ω) :=
    ginibreBrownianOU_step_ae B P hB rate s t 0
  have hc : covariance X (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 (s+t)) P =
      covariance X (fun ω => ginibreOUDecay rate t * X ω + Y ω) P := by
    unfold covariance
    rw [integral_congr_ae he]
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    rw [hω]
  rw [hc]
  change covariance X ((ginibreOUDecay rate t) • X + Y) P = _
  rw [covariance_add_right hX (hX.const_smul _) hY, covariance_smul_right]
  have hi : covariance X Y P = 0 :=
    (ginibreBrownianOUInnovation_independent_value B P hB rate s t 0).symm.covariance_eq_zero hX hY
  rw [hi,add_zero,covariance_self hX.aemeasurable]
  have hv := (ginibreBrownianOU_zero_hasLaw B P hB rate s).variance_eq
  simpa [X,id_def,ginibreOUTransition] using congrArg (fun v : ℝ => ginibreOUDecay rate t * v) hv

theorem ginibreBrownianOU_zero_independent_initial {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (Z : Ω → ℝ) (hind : IndepFun Z (fun ω t => B t ω) P) (rate t : ℝ≥0) :
    IndepFun Z (ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t) P := by
  have h := hind.comp measurable_id (ginibreOUConvolutionFunctional_measurable rate t)
  exact h.congr (Filter.Eventually.of_forall (fun _ => rfl))
    (ginibreOUConvolutionFunctional_ae_eq B P hB rate t)

theorem ginibreBrownianOU_stationary_covariance_step {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate s t : ℝ≥0) :
    covariance (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) s ω)
      (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) (s+t) ω) P =
      ginibreOUDecay rate t / 2 := by
  let X (u : ℝ≥0) := ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 u
  have hX (u : ℝ≥0) : MemLp (X u) 2 P :=
    (ginibreBrownianOU_zero_isGaussianProcess B P hB rate).hasGaussianLaw_eval u |>.memLp_two
  have hZm : MemLp Z 2 P := hZ.hasGaussianLaw.memLp_two
  have hcross (u : ℝ≥0) : covariance Z (X u) P = 0 :=
    (ginibreBrownianOU_zero_independent_initial B P hB Z hind rate u).covariance_eq_zero hZm (hX u)
  have hvar : variance Z P = (1/2 : ℝ) := by
    simpa [id_def] using hZ.variance_eq
  have hs (u : ℝ≥0) : (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) u ω) =
      ginibreOUDecay rate u • Z + X u := by
    funext ω
    change drivenOUPath rate (Z ω) (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) u = _
    rw [drivenOUPath_initial_split]
    rfl
  have hst := hs (s+t)
  simp only [NNReal.coe_add] at hst
  rw [hs s,hst,covariance_add_left (hZm.const_smul _) (hX s)
    ((hZm.const_smul _).add (hX (s+t))),
    covariance_add_right (hZm.const_smul _) (hZm.const_smul _) (hX (s+t)),
    covariance_add_right (hX s) (hZm.const_smul _) (hX (s+t))]
  rw [covariance_smul_left,covariance_smul_right,covariance_self hZm.aemeasurable,hvar,
    covariance_smul_left,hcross, mul_zero,covariance_smul_right,
    covariance_comm (X s) Z,hcross,mul_zero]
  have hc : covariance (X s) (X (s+t)) P = ginibreOUDecay rate t * (ginibreOUVariance rate s : ℝ) := by
    simpa [X,NNReal.coe_add] using ginibreBrownianOU_zero_covariance_step B P hB rate s t
  rw [hc,
    ginibreOUDecay_add,ginibreOUVariance_coe]
  ring

theorem ginibreBrownianOU_stationary_mean {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (rate t : ℝ≥0) :
    (∫ ω, ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t ω ∂P)=0 := by
  have he : (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t ω) =
      (fun ω => ginibreOUDecay rate t * Z ω + ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t ω) := by
    funext ω
    change drivenOUPath rate (Z ω) (ginibreBrownianNoise B (Real.sqrt (rate : ℝ)) ω) t = _
    rw [drivenOUPath_initial_split]
    rfl
  rw [he,integral_add (hZ.hasGaussianLaw.integrable.const_mul _)
    ((ginibreBrownianOU_zero_isGaussianProcess B P hB rate).hasGaussianLaw_eval t).integrable,
    integral_const_mul]
  have hm : (∫ ω, Z ω ∂P)=0 := by simpa using hZ.integral_eq
  have hmX : (∫ ω, ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) 0 t ω ∂P)=0 := by
    simpa [ginibreOUTransition] using (ginibreBrownianOU_zero_hasLaw B P hB rate t).integral_eq
  rw [hm,hmX,mul_zero,add_zero]

theorem ginibreBrownianOU_stationary_covariance {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (rate s t : ℝ≥0) :
    covariance (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) s ω)
      (fun ω => ginibreBrownianOU B rate (Real.sqrt (rate : ℝ)) (Z ω) t ω) P =
      ginibreOUDecay rate (max s t-min s t) / 2 := by
  rcases le_total s t with h | h
  · have ht : s+(t-s)=t := add_tsub_cancel_of_le h
    have hx := ginibreBrownianOU_stationary_covariance_step B P hB Z hZ hind rate s (t-s)
    rw [← NNReal.coe_add,ht] at hx
    simpa [max_eq_right h,min_eq_left h] using hx
  · rw [covariance_comm]
    have ht : t+(s-t)=s := add_tsub_cancel_of_le h
    have hx := ginibreBrownianOU_stationary_covariance_step B P hB Z hZ hind rate t (s-t)
    rw [← NNReal.coe_add,ht] at hx
    simpa [max_eq_left h,min_eq_right h] using hx

end
end GinibrePoincare
