module

public import GinibrePoincare.Analysis.GinibreHamiltonianOUActionWeight
public import GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsGenerator

@[expose] public section

/-! # The concrete Gibbs action relative to stationary unit-diffusion OU

The reference confinement is `n * configurationNormSq`, whose actual OU
reference has drift `-2n x` and noise amplitude `sqrt 2`. The relative
potential is arbitrary C². These action and weighted reference-law identities
are the time-reversal layer; identifying the action with the killed gradient
SDE is a further stochastic step.
-/

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ContDiff Topology BigOperators
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

local instance bakryGibbsReversal_fullMeasurable (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance bakryGibbsReversal_fullBorel (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
local instance bakryGibbsReversal_compactMeasurable (n : ℕ) (T : ℝ) : MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance bakryGibbsReversal_compactBorel (n : ℕ) (T : ℝ) : BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩

/-- Actual potential relative to the stationary unit-diffusion OU reference. -/
def bakryEmeryGibbsRelativePotential {n : ℕ} (W : Configuration n → ℝ) (z : Configuration n) : ℝ :=
  W z - (n : ℝ) * configurationNormSq z

/-- Ordinary Euclidean Laplacian in the real and imaginary coordinates. -/
def bakryEmeryGibbsConfigurationLaplacian {n : ℕ} (S : Configuration n → ℝ)
    (z : Configuration n) : ℝ :=
  ∑ j, (fderiv ℝ (fun w => fderiv ℝ S w (realCoordinateDirection j)) z
    (realCoordinateDirection j) +
    fderiv ℝ (fun w => fderiv ℝ S w (imaginaryCoordinateDirection j)) z
    (imaginaryCoordinateDirection j))

def bakryEmeryGibbsConfigurationGradientSq {n : ℕ} (S : Configuration n → ℝ)
    (z : Configuration n) : ℝ :=
  ∑ j, ((fderiv ℝ S z (realCoordinateDirection j)) ^ 2 +
    (fderiv ℝ S z (imaginaryCoordinateDirection j)) ^ 2)

def bakryEmeryGibbsConfigurationRadialGradient {n : ℕ} (S : Configuration n → ℝ)
    (z : Configuration n) : ℝ :=
  ∑ j, ((z j).re * fderiv ℝ S z (realCoordinateDirection j) +
    (z j).im * fderiv ℝ S z (imaginaryCoordinateDirection j))

/-- Exact OU-relative potential term `ΔS/2-n<x,∇S>-|∇S|²/4`. -/
def bakryEmeryGibbsOUActionIntegrand {n : ℕ} (W : Configuration n → ℝ)
    (z : Configuration n) : ℝ :=
  let S := bakryEmeryGibbsRelativePotential W
  bakryEmeryGibbsConfigurationLaplacian S z / 2 -
    (n : ℝ) * bakryEmeryGibbsConfigurationRadialGradient S z -
    bakryEmeryGibbsConfigurationGradientSq S z / 4

private theorem gibbsRelative_contDiff {n : ℕ} {W : Configuration n → ℝ}
    (hW : ContDiff ℝ 2 W) : ContDiff ℝ 2 (bakryEmeryGibbsRelativePotential W) :=
  hW.sub (contDiff_const.mul (contDiff_configurationNormSq.of_le (by simp)))

/-- The relative action's integrand is a genuine continuous function for C² confinement. -/
theorem bakryEmeryGibbsOUActionIntegrand_continuous {n : ℕ} {W : Configuration n → ℝ}
    (hW : ContDiff ℝ 2 W) : Continuous (bakryEmeryGibbsOUActionIntegrand W) := by
  have hS := gibbsRelative_contDiff hW
  have hd : ContDiff ℝ 1 (fderiv ℝ (bakryEmeryGibbsRelativePotential W)) :=
    hS.fderiv_right (by norm_num)
  have hv (v : Configuration n) : ContDiff ℝ 1
      (fun z => fderiv ℝ (bakryEmeryGibbsRelativePotential W) z v) :=
    hd.clm_apply contDiff_const
  have hsecond (v : Configuration n) : Continuous
      (fun z => fderiv ℝ (fun w => fderiv ℝ (bakryEmeryGibbsRelativePotential W) w v) z v) :=
    ((hv v).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  unfold bakryEmeryGibbsOUActionIntegrand bakryEmeryGibbsConfigurationLaplacian
    bakryEmeryGibbsConfigurationRadialGradient bakryEmeryGibbsConfigurationGradientSq
  apply Continuous.sub
  · apply Continuous.sub
    · exact (continuous_finsetSum _ (fun j _ => (hsecond _).add (hsecond _))).div_const 2
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro j _
      exact ((Complex.continuous_re.comp (continuous_apply j)).mul (hv _).continuous).add
        ((Complex.continuous_im.comp (continuous_apply j)).mul (hv _).continuous)
  · exact (continuous_finsetSum _ (fun j _ => ((hv _).continuous.pow 2).add
      ((hv _).continuous.pow 2))).div_const 4

/-- Actual symmetric endpoint-plus-action density on full continuous paths. -/
def bakryEmeryGibbsOUFullAction {n : ℕ} (W : Configuration n → ℝ) (T : ℝ)
    (x : C(ℝ, Configuration n)) : ENNReal :=
  gradientPathReversalWeight T (bakryEmeryGibbsRelativePotential W)
    (bakryEmeryGibbsOUActionIntegrand W) x

theorem bakryEmeryGibbsOUFullAction_measurable {n : ℕ} {W : Configuration n → ℝ}
    (hW : ContDiff ℝ 2 W) (T : ℝ) : Measurable (bakryEmeryGibbsOUFullAction W T) := by
  have hS := (gibbsRelative_contDiff hW).continuous.measurable
  have hA := (bakryEmeryGibbsOUActionIntegrand_continuous hW).measurable
  have hm : Measurable (fun p : C(ℝ, Configuration n) × ℝ =>
      bakryEmeryGibbsOUActionIntegrand W (p.1 p.2)) := hA.comp continuous_eval.measurable
  have hi (s : Set ℝ) : Measurable (fun x : C(ℝ, Configuration n) =>
      ∫ t in s, bakryEmeryGibbsOUActionIntegrand W (x t)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : Measurable (fun x : C(ℝ, Configuration n) =>
      ∫ t in (0 : ℝ)..T, bakryEmeryGibbsOUActionIntegrand W (x t)) :=
    (hi _).sub (hi _)
  exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
    (((((hS.comp (continuous_eval_const 0).measurable).add
      (hS.comp (continuous_eval_const T).measurable)).neg.div_const 2).add he)))

/-- The relative action on a compact path, using the canonical continuous extension. -/
def bakryEmeryGibbsOUAction {n : ℕ} (W : Configuration n → ℝ) (T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) : ENNReal :=
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  bakryEmeryGibbsOUFullAction W T (ContinuousMap.IccExtendCM x)

theorem bakryEmeryGibbsOUAction_measurable {n : ℕ} {W : Configuration n → ℝ}
    (hW : ContDiff ℝ 2 W) (T : ℝ) (hT : 0 ≤ T) :
    Measurable (bakryEmeryGibbsOUAction W T hT) := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  exact (bakryEmeryGibbsOUFullAction_measurable hW T).comp
    (ContinuousMap.IccExtendCM : C(C(Icc (0 : ℝ) T, Configuration n), C(ℝ, Configuration n))).continuous.measurable

theorem bakryEmeryGibbsOUAction_reverse {n : ℕ} (W : Configuration n → ℝ)
    (T : ℝ) (hT : 0 ≤ T) (x : C(Icc (0 : ℝ) T, Configuration n)) :
    bakryEmeryGibbsOUAction W T hT (x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
      bakryEmeryGibbsOUAction W T hT x := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  unfold bakryEmeryGibbsOUAction bakryEmeryGibbsOUFullAction
  change gradientPathReversalWeight T _ _
    (fun s => ContinuousMap.IccExtendCM (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) = _
  rw [ginibreHamiltonianCompactExtend_reverse, gradientPathReversalWeight_reverse]

/-- True stationary unit-diffusion OU path law, reweighted by the concrete
C² confinement action, is invariant under time reversal. -/
theorem bakryEmeryGibbsOUActionMeasure_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) {W : Configuration n → ℝ} (hW : ContDiff ℝ 2 W)
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun sample t => B t sample) P) (T : ℝ≥0) :
    ((ginibreConfigurationOUReferenceLaw n B P Z (2 * (n : ℝ≥0)) T).withDensity
      (bakryEmeryGibbsOUAction W T T.property)).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime T T.property)) =
    (ginibreConfigurationOUReferenceLaw n B P Z (2 * (n : ℝ≥0)) T).withDensity
      (bakryEmeryGibbsOUAction W T T.property) := by
  exact invariant_measure_withDensity_of_invariant_weight _ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T T.property)).measurable
    (ginibreConfigurationOUReferenceLaw_reverse n B P hB Z hZ hind _ T) _
    (bakryEmeryGibbsOUAction_measurable hW T T.property)
    (bakryEmeryGibbsOUAction_reverse W T T.property)

#print axioms bakryEmeryGibbsOUActionIntegrand_continuous
#print axioms bakryEmeryGibbsOUFullAction_measurable
#print axioms bakryEmeryGibbsOUAction_measurable
#print axioms bakryEmeryGibbsOUAction_reverse
#print axioms bakryEmeryGibbsOUActionMeasure_reverse

end
end GinibrePoincare
