module
public import GinibrePoincare.Analysis.CorrespondenceOperatorStochasticSemigroup
public import GinibrePoincare.Analysis.CorrespondenceOperatorConservation
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGlobal
@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The actual unrestricted diffusion contracts the essential sup norm.
The Brownian representation is supplied by an internally constructed canonical
Brownian probability space, not by an existence hypothesis. -/
theorem correspondenceOperatorRealEvolution_essential_bound (n : ℕ) (hn : 0<n)
    (t : ℝ≥0) (f : GinibreFullValueL2 n) (A : ℝ) (hA : 0≤A)
    (hf : ∀ᵐ z ∂ginibreMeasure n, ‖f z‖≤A) :
    ∀ᵐ z ∂ginibreMeasure n, ‖(correspondenceOperatorRealEvolution n hn t f) z‖≤A := by
  let ι := Fin n × Fin 2
  let P := bakryBrownianCoordinateMeasure ι
  let B := bakryBrownianCoordinateProcess ι
  have hB := bakryBrownianCoordinate_isBrownian ι
  have hiB := bakryBrownianCoordinate_independent ι
  obtain ⟨v, hv, hvb, hfv⟩ := ginibreBoundedLp_measurable_version hn f A hf
  rw [max_eq_left hA] at hvb
  obtain ⟨hrm, hrb, hfr⟩ := ginibreOriginalStochasticL2Operator_bounded_representative hn
    (n : ℝ≥0) P B hB hiB t f v hfv hv A hvb
  have hEq := correspondenceOperator_stochastic_semigroup_eq hn (n : ℝ≥0) P B hB hiB t
  have hn' : (n : ℝ≥0)≠0 := by exact_mod_cast hn.ne'
  rw [div_self hn', one_mul] at hEq
  rw [hEq] at hfr
  filter_upwards [hfr] with z hz
  rw [hz]
  exact hrb z

/-- Conservation on the actual unrestricted real L² space. -/
theorem correspondenceOperatorRealEvolution_constant (n : ℕ) (hn : 0<n)
    (t : ℝ≥0) (c : ℝ) :
    correspondenceOperatorRealEvolution n hn t (ginibreRealConstantL2 n hn c)=
      ginibreRealConstantL2 n hn c := by
  have hc : ginibreFullComplexOfReal n (ginibreRealConstantL2 n hn c)=
      (ginibreFullConstant n hn (c : ℂ)).val := by
    apply Lp.ext
    filter_upwards [ginibreFullComplexOfReal_ae n (ginibreRealConstantL2 n hn c),
      ginibreRealConstantL2_ae n hn c, ginibreFullConstant_ae n hn (c : ℂ)] with z hz hv hh
    rw [hz, hv, hh]
  have he := correspondenceOperatorEvolution_constant n hn t (c : ℂ)
  rw [← hc, correspondenceOperatorEvolution_ofReal] at he
  have hr := congrArg (ginibreFullComplexRe n) he
  simpa using hr

/-- The unrestricted semigroup preserves every bounded order interval;
in particular it is Markov on [0,1]. -/
theorem correspondenceOperatorRealEvolution_interval (n : ℕ) (hn : 0<n)
    (t : ℝ≥0) (f : GinibreFullValueL2 n) (a b : ℝ) (hab : a≤b)
    (hf : ∀ᵐ z ∂ginibreMeasure n, f z∈Set.Icc a b) :
    ∀ᵐ z ∂ginibreMeasure n, (correspondenceOperatorRealEvolution n hn t f) z∈Set.Icc a b := by
  let c := (a+b)/2
  let r := (b-a)/2
  let k := ginibreRealConstantL2 n hn c
  have hr : 0≤r := by dsimp [r]; linarith
  have hbound : ∀ᵐ z ∂ginibreMeasure n, ‖(f-k) z‖≤r := by
    filter_upwards [hf, Lp.coeFn_sub f k, ginibreRealConstantL2_ae n hn c] with z hz hsub hk
    change k z=c at hk
    rw [hsub, Pi.sub_apply, hk, Real.norm_eq_abs]
    rw [abs_le]
    dsimp [r, c]
    constructor <;> linarith [hz.1, hz.2]
  have hout := correspondenceOperatorRealEvolution_essential_bound n hn t (f-k) r hr hbound
  have he : correspondenceOperatorRealEvolution n hn t (f-k)=
      correspondenceOperatorRealEvolution n hn t f-k := by
    rw [map_sub, correspondenceOperatorRealEvolution_constant]
  rw [he] at hout
  filter_upwards [hout, Lp.coeFn_sub (correspondenceOperatorRealEvolution n hn t f) k,
    ginibreRealConstantL2_ae n hn c] with z hz hsub hk
  change k z=c at hk
  rw [hsub, Pi.sub_apply, hk, Real.norm_eq_abs, abs_le] at hz
  constructor <;> dsimp [r, c] at hz <;> linarith [hz.1, hz.2]

#print axioms correspondenceOperatorRealEvolution_essential_bound
#print axioms correspondenceOperatorRealEvolution_interval
end
end GinibrePoincare
