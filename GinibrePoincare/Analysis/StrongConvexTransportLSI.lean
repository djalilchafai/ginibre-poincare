module

public import GinibrePoincare.Analysis.StrongConvexQuantileTransport
public import GinibrePoincare.Analysis.GaussianLSIReal
public import GinibrePoincare.Analysis.GinibreEntropy

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A genuine differentiable transport with bounded derivative transfers the
sharp standard Gaussian logarithmic Sobolev inequality to its actual image
measure. No target entropy or Sobolev inequality is assumed. -/
theorem standardGaussian_transport_lsi (ν : Measure ℝ) (T : ℝ → ℝ)
    (hT : ContDiff ℝ 1 T) (hmap : (gaussianReal 0 1).map T = ν)
    (L : ℝ) (hL : 0 ≤ L) (hbound : ∀ x, |deriv T x| ≤ L)
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f)
    (hfl : MemLp f 2 ν) (hfd : MemLp (deriv f) 2 ν) :
    Integrable (fun x => f x ^ 2 * Real.log (f x ^ 2)) ν ∧
      squareEntropy ν f ≤ (2 * L ^ 2) * ∫ x, (deriv f x) ^ 2 ∂ν := by
  let H := f ∘ T
  have hH : ContDiff ℝ 1 H := hf.comp hT
  have hpres : MeasurePreserving T (gaussianReal 0 1) ν := ⟨hT.continuous.measurable, hmap⟩
  have hHl : MemLp H 2 (gaussianReal 0 1) := hfl.comp_measurePreserving hpres
  have hdsq : Integrable (fun x => (deriv f (T x)) ^ 2) (gaussianReal 0 1) := by
    exact hpres.integrable_comp_of_integrable
      ((memLp_two_iff_integrable_sq hfd.aestronglyMeasurable).mp hfd)
  have hchain (x : ℝ) : deriv H x = deriv f (T x) * deriv T x := by
    exact ((hf.differentiable (by norm_num) (T x)).hasDerivAt.comp x
      ((hT.differentiable (by norm_num) x).hasDerivAt)).deriv
  have hsquare (x : ℝ) : (deriv H x) ^ 2 ≤ L ^ 2 * (deriv f (T x)) ^ 2 := by
    rw [hchain, mul_pow]
    have hb : (deriv T x) ^ 2 ≤ L ^ 2 := by
      nlinarith [hbound x, sq_abs (deriv T x), abs_nonneg (deriv T x)]
    exact (mul_le_mul_of_nonneg_left hb (sq_nonneg (deriv f (T x)))).trans_eq (mul_comm _ _)
  have hdmeas : Measurable (deriv H) := (hH.continuous_deriv (by norm_num)).measurable
  have hdint : Integrable (fun x => (deriv H x) ^ 2) (gaussianReal 0 1) := by
    apply (hdsq.const_mul (L ^ 2)).mono' (hdmeas.pow_const 2).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hsquare x
  have hHd : MemLp (deriv H) 2 (gaussianReal 0 1) :=
    (memLp_two_iff_integrable_sq hdmeas.aestronglyMeasurable).mpr hdint
  obtain ⟨hlog, hlsi⟩ := gaussianReal_lsi_C1 H hH hHl hHd
  have hlogMeas : Measurable (fun x => f x ^ 2 * Real.log (f x ^ 2)) :=
    ((hf.continuous.measurable.pow_const 2).mul (hf.continuous.measurable.pow_const 2).log)
  refine ⟨(hpres.integrable_comp hlogMeas.aestronglyMeasurable).mp hlog, ?_⟩
  have hent : squareEntropy ν f = squareEntropy (gaussianReal 0 1) H := by
    rw [← hmap]
    exact squareEntropy_map _ _ hT.continuous.measurable.aemeasurable f
      (hf.continuous.measurable.pow_const 2).aestronglyMeasurable hlogMeas.aestronglyMeasurable
  rw [hent]
  have he : (∫ x, (deriv H x) ^ 2 ∂gaussianReal 0 1) ≤
      L ^ 2 * ∫ x, (deriv f x) ^ 2 ∂ν := by
    calc
      _ ≤ ∫ x, L ^ 2 * (deriv f (T x)) ^ 2 ∂gaussianReal 0 1 :=
        integral_mono_ae hdint (hdsq.const_mul _) (Filter.Eventually.of_forall hsquare)
      _ = _ := by
        rw [integral_const_mul, ← hmap, integral_map hT.continuous.measurable.aemeasurable
          ((hf.continuous_deriv (by norm_num)).measurable.pow_const 2).aestronglyMeasurable]
  calc
    _ ≤ 2 * ∫ x, (deriv H x) ^ 2 ∂gaussianReal 0 1 := hlsi
    _ ≤ 2 * (L ^ 2 * ∫ x, (deriv f x) ^ 2 ∂ν) := mul_le_mul_of_nonneg_left he (by norm_num)
    _ = _ := by ring

#print axioms standardGaussian_transport_lsi
end
end GinibrePoincare
