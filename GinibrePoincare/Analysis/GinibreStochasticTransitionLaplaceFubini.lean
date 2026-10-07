module

public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

open MeasureTheory Set
namespace GinibrePoincare
noncomputable section

/-- Ordinary Bochner Fubini for a genuinely integrable initial value and a
jointly measurable uniformly bounded transition mean. -/
theorem boundedTransitionMean_laplace_fubini {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (f : E → ℝ) (hf : Integrable f μ)
    (m : ℝ × E → ℝ) (hm : Measurable m) (C : ℝ) (hC : ∀ p, ‖m p‖≤C)
    {c : ℝ} (hc : 0<c) :
    (∫ t in Ioi (0:ℝ), ∫ z, f z*(Real.exp (-c*t)*m (t,z)) ∂μ)=
      ∫ z, f z*(∫ t in Ioi (0:ℝ), Real.exp (-c*t)*m (t,z)) ∂μ := by
  let ν := volume.restrict (Ioi (0:ℝ))
  have he : Integrable (fun t : ℝ => Real.exp (-c*t)) ν :=
    integrableOn_exp_mul_Ioi (show -c<0 by linarith) 0
  have hs : AEStronglyMeasurable (fun p : ℝ × E => f p.2*(Real.exp (-c*p.1)*m p)) (ν.prod μ) :=
    (hf.aestronglyMeasurable.comp_snd).mul
      (((Real.measurable_exp.comp (measurable_const.mul measurable_fst)).mul hm).aestronglyMeasurable)
  have hi : Integrable (fun p : ℝ × E => f p.2*(Real.exp (-c*p.1)*m p)) (ν.prod μ) := by
    apply ((he.mul_prod hf.norm).mul_const C).mono' hs
    exact ae_of_all _ fun p => by
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      calc
        ‖f p.2‖*(Real.exp (-c*p.1)*‖m p‖) ≤ ‖f p.2‖*(Real.exp (-c*p.1)*C) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hC p) (Real.exp_pos _).le) (norm_nonneg _)
        _ = (Real.exp (-c*p.1)*‖f p.2‖)*C := by ring
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact ae_of_all _ fun z => integral_const_mul (f z) _

#print axioms boundedTransitionMean_laplace_fubini
end
end GinibrePoincare
