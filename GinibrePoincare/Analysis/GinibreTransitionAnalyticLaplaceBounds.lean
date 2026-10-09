module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLaplaceOrbit

@[expose] public section

open MeasureTheory Set
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The genuine positive normalized exponential weight has mass one. -/
theorem actualNormalizedLaplaceWeight_mass (c : ℝ) (hc : 0<c) :
    (∫ t in Ioi (0 : ℝ), c*Real.exp (-c*t))=1 := by
  rw [integral_const_mul]
  have h := integral_exp_mul_Ioi (show -c<0 by linarith) 0
  rw [h]
  simp only [mul_zero, Real.exp_zero]
  field_simp

theorem actualNormalizedLaplaceWeight_integrable (c : ℝ) (hc : 0<c) :
    IntegrableOn (fun t : ℝ => c*Real.exp (-c*t)) (Ioi 0) :=
  (integrableOn_exp_mul_Ioi (show -c<0 by linarith) 0).const_mul c

/-- A genuinely bounded measurable orbit has a bounded normalized Laplace
integral, with the exact same bound. -/
theorem actualNormalizedLaplaceIntegral_norm_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ → E) (c A : ℝ) (hc : 0<c)
    (ha : AEStronglyMeasurable a (volume.restrict (Ioi 0)))
    (hb : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖a t‖≤A) :
    IntegrableOn (fun t : ℝ => (c*Real.exp (-c*t)) • a t) (Ioi 0) ∧
      ‖∫ t in Ioi (0 : ℝ), (c*Real.exp (-c*t)) • a t‖≤A := by
  let w := fun t : ℝ => c*Real.exp (-c*t)
  have hw := actualNormalizedLaplaceWeight_integrable c hc
  have hmeas : AEStronglyMeasurable (fun t => w t • a t) (volume.restrict (Ioi 0)) :=
    hw.aestronglyMeasurable.smul ha
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0), ‖w t • a t‖≤A*w t := by
    filter_upwards [hb] with t ht
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hc.le (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_left ht (mul_nonneg hc.le (Real.exp_pos _).le)).trans_eq (mul_comm _ _)
  have hi := (hw.const_mul A).mono' hmeas hbound
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖w t • a t‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), A*w t := integral_mono_ae hi.norm (hw.const_mul A) hbound
    _ = A := by rw [integral_const_mul, actualNormalizedLaplaceWeight_mass c hc, mul_one]

#print axioms actualNormalizedLaplaceWeight_mass
#print axioms actualNormalizedLaplaceWeight_integrable
#print axioms actualNormalizedLaplaceIntegral_norm_bound
end
end GinibrePoincare
