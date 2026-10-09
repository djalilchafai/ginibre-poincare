module

public import GinibrePoincare.Analysis.BrownianStoppingExitPastNoisePath
public import GinibrePoincare.Analysis.GinibreDrivenPathOUShift
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! The actual global reference OU path driven by the original configuration
Brownian family, with genuine completed-past adaptation. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

local instance GinibreHamiltonianOUReferenceProcess_measurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance GinibreHamiltonianOUReferenceProcess_borel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

def ginibreHamiltonianOUValue (n : ℕ) (α : ℝ) (z : Configuration n) (t : ℝ≥0)
    (N : GinibreContinuousNoise n) : Configuration n :=
  drivenOUPath (2*α/(n : ℝ)) z N.val t

theorem ginibreHamiltonianOUValue_measurable (n : ℕ) (α : ℝ) (z : Configuration n) (t : ℝ≥0) :
    Measurable (ginibreHamiltonianOUValue n α z t) := by
  have hj : Continuous (fun p : C(ℝ, Configuration n) × ℝ => Real.exp ((2*α/(n : ℝ))*p.2) • p.1 p.2) :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_snd)).smul continuous_eval
  have hInt : Measurable (fun N : C(ℝ, Configuration n) => ∫ s in (0 : ℝ)..(t : ℝ),
      Real.exp ((2*α/(n : ℝ))*s) • N s) := by
    have hi := hj.measurable.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg] using hi.measurable
  have hInner : Measurable (fun N : C(ℝ, Configuration n) => z-(2*α/(n : ℝ)) •
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((2*α/(n : ℝ))*s) • N s) :=
    measurable_const.sub (hInt.const_smul (2*α/(n : ℝ)))
  have hV : Measurable (fun N : C(ℝ, Configuration n) => N (t : ℝ)+
      Real.exp (-(2*α/(n : ℝ))*(t : ℝ)) • (z-(2*α/(n : ℝ)) •
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp ((2*α/(n : ℝ))*s) • N s)) :=
    (continuous_eval_const (t : ℝ)).measurable.add (hInner.const_smul (Real.exp (-(2*α/(n : ℝ))*(t : ℝ))))
  have hsub : Continuous (fun N : GinibreContinuousNoise n => N.val) := continuous_subtype_val
  exact hV.comp hsub.measurable

def ginibreHamiltonianOUReferenceProcess {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : Configuration n :=
  ginibreHamiltonianOUValue n α z t (ginibreBrownianFullContinuousNoise n B α ω)

theorem ginibreHamiltonianOUReferenceProcess_zero {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    ginibreHamiltonianOUReferenceProcess n α z B 0 ω = z := by
  simp [ginibreHamiltonianOUReferenceProcess, ginibreHamiltonianOUValue, drivenOUPath,
    (ginibreBrownianFullContinuousNoise n B α ω).property]

theorem ginibreHamiltonianOUReferenceProcess_continuous {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    Continuous (fun t => ginibreHamiltonianOUReferenceProcess n α z B t ω) :=
  (drivenOUPath_continuous _ z _ (ginibreBrownianFullContinuousNoise n B α ω).val.continuous).comp NNReal.continuous_coe

theorem ginibreHamiltonianOUReferenceProcess_stronglyAdapted {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
      (ginibreHamiltonianOUReferenceProcess n α z B) := by
  intro s
  have hAE₁ := ginibreBrownianFullContinuousNoise_ae n B P hB α
  have hAE₂ := ginibreBrownianFullPastContinuousNoise_ae n B P hB α s
  have hm := ginibreBrownianFamilyPastSpace_le B P (fun i => (hB i).toIsPreBrownianReal) s
  let mPast := ginibreBrownianFamilyPastSpace B s
  let mAug := ginibreNullAugmentation (mAmbient := mAmbient) P mPast
  have hAug := ginibreNullAugmentation_le (mAmbient := mAmbient) P mPast hm
  let μ := P.trim hAug
  haveI : μ.IsComplete := ginibreNullAugmentation_trim_complete (mAmbient := mAmbient) P mPast hm
  have hPast : @Measurable Ω (Configuration n) mAug _ (fun ω =>
      ginibreHamiltonianOUValue n α z s (ginibreBrownianFullPastContinuousNoise n B α s ω)) :=
    (ginibreHamiltonianOUValue_measurable n α z s).comp
      (ginibreBrownianFullPastContinuousNoise_measurable (mAmbient := mAmbient) n B P hB α s)
  have hAE := ginibreNullAugmentation_ae_transfer (mAmbient := mAmbient) P mPast hm _
    (hAE₁.and hAE₂)
  have heq : (fun ω => ginibreHamiltonianOUValue n α z s
      (ginibreBrownianFullPastContinuousNoise n B α s ω)) =ᵐ[μ]
      ginibreHamiltonianOUReferenceProcess n α z B s := by
    filter_upwards [hAE] with ω hω
    apply drivenOUPath_congr_nonneg _ z _ _ (s : ℝ) s.property
    intro u hu
    rw [hω.2 u, hω.1 u, min_eq_left hu.2]
  exact ((aemeasurable_iff_measurable (μ := μ)).mp
    (hPast.aemeasurable.congr heq)).stronglyMeasurable

theorem ginibreHamiltonianOUReferenceProcess_original_equation {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, ginibreHamiltonianOUReferenceProcess n α z B t ω =
      z+ginibreConfigurationBrownianNoise n B α ω t+
      ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) •
        ginibreHamiltonianOUReferenceProcess n α z B s.toNNReal ω := by
  filter_upwards [ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hω
  intro t
  have h := drivenOUPath_integral_equation (2*α/(n : ℝ)) z
    (ginibreBrownianFullContinuousNoise n B α ω).val
    (ginibreBrownianFullContinuousNoise n B α ω).val.continuous (t : ℝ)
  change ginibreHamiltonianOUReferenceProcess n α z B t ω = _ at h
  rw [h, hω]
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hs0 : 0 ≤ s := by
    have hh : s ∈ Icc (0 : ℝ) (t : ℝ) := by simpa only [uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
    exact hh.1
  unfold ginibreHamiltonianOUReferenceProcess ginibreHamiltonianOUValue
  dsimp only
  rw [Real.coe_toNNReal _ hs0]
  congr 1
  ring

#print axioms ginibreHamiltonianOUReferenceProcess_stronglyAdapted
#print axioms ginibreHamiltonianOUReferenceProcess_original_equation
end
end GinibrePoincare
