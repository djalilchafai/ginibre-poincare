module

public import Mathlib.Probability.Kernel.WithDensity
public import Mathlib.Probability.Kernel.Composition.MeasureComp

@[expose] public section

/-! Genuine Metropolis kernels: symmetric accepted flux and explicit probability normalization. -/
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000

def metropolisAcceptedFlux {E : Type*} (q : E → E → ℝ≥0∞) (x y : E) : ℝ≥0∞ := min (q x y) (q y x)

theorem metropolisAcceptedFlux_measurable {E : Type*} [MeasurableSpace E]
    (q : E → E → ℝ≥0∞) (hq : Measurable (Function.uncurry q)) :
    Measurable (Function.uncurry (metropolisAcceptedFlux q)) :=
  hq.min (hq.comp measurable_swap)

def metropolisRejectionMass {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (q : E → E → ℝ≥0∞) (x : E) : ℝ≥0∞ := 1-∫⁻ y, metropolisAcceptedFlux q x y ∂μ

def metropolisReversibleKernel {E : Type*} [MeasurableSpace E] (μ : Measure E) [SFinite μ]
    (q : E → E → ℝ≥0∞) : Kernel E E :=
  (Kernel.const E μ).withDensity (metropolisAcceptedFlux q)+
    Kernel.id.withDensity (fun x _ => metropolisRejectionMass μ q x)

theorem metropolisRejectionMass_measurable {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (q : E → E → ℝ≥0∞) (hq : Measurable (Function.uncurry q)) :
    Measurable (metropolisRejectionMass μ q) :=
  measurable_const.sub (metropolisAcceptedFlux_measurable q hq).lintegral_prod_right

theorem metropolisReversibleKernel_apply {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (q : E → E → ℝ≥0∞)
    (hq : Measurable (Function.uncurry q)) (x : E) :
    metropolisReversibleKernel μ q x = μ.withDensity (metropolisAcceptedFlux q x)+
      metropolisRejectionMass μ q x • Measure.dirac x := by
  have hr : Measurable (Function.uncurry (fun x (_ : E) => metropolisRejectionMass μ q x)) :=
    (metropolisRejectionMass_measurable μ q hq).comp measurable_fst
  rw [metropolisReversibleKernel,Kernel.add_apply,
    Kernel.withDensity_apply _ (metropolisAcceptedFlux_measurable q hq),Kernel.const_apply,
    Kernel.withDensity_apply _ hr,Kernel.id_apply,dirac_withDensity' measurable_const]

theorem metropolisReversibleKernel_isMarkov {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (q : E → E → ℝ≥0∞)
    (hq : Measurable (Function.uncurry q)) (hNorm : ∀ x, ∫⁻ y, q x y ∂μ=1) :
    IsMarkovKernel (metropolisReversibleKernel μ q) := by
  constructor
  intro x
  constructor
  rw [metropolisReversibleKernel_apply μ q hq,Measure.add_apply,withDensity_apply' _ univ,
    Measure.smul_apply,Measure.dirac_apply_of_mem (mem_univ x),smul_eq_mul,mul_one,setLIntegral_univ,
    metropolisRejectionMass]
  exact add_tsub_cancel_of_le (by
    calc
      (∫⁻ y, metropolisAcceptedFlux q x y ∂μ) ≤ ∫⁻ y, q x y ∂μ := lintegral_mono (fun y => min_le_left _ _)
      _=1 := hNorm x)

theorem metropolisAcceptedFlux_balance {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (q : E → E → ℝ≥0∞) (φ : E × E → ℝ≥0∞) :
    (∫⁻ p, metropolisAcceptedFlux q p.1 p.2*φ p ∂μ.prod μ) =
      ∫⁻ p, metropolisAcceptedFlux q p.1 p.2*φ p.swap ∂μ.prod μ := by
  rw [← MeasureTheory.lintegral_prod_swap (μ := μ) (ν := μ)
    (fun p => metropolisAcceptedFlux q p.1 p.2*φ p)]
  apply lintegral_congr
  intro p
  simp only [metropolisAcceptedFlux,Prod.fst_swap,Prod.snd_swap,min_comm]

end
end GinibrePoincare
