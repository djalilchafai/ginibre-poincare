module
public import GinibrePoincare.Analysis.AlternativeBakryEmeryBrownianGrid
public import GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath
public import Mathlib.Analysis.InnerProductSpace.PiL2
@[expose] public section
open MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]

/-- The actual unscaled independent coordinate Brownian driving path. -/
def bakryEmeryBrownianNoiseReal (B : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) :
    EuclideanSpace ℝ ι := WithLp.toLp 2 (fun i => B i t.toNNReal ω)

theorem bakryEmeryBrownianNoiseReal_actual (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, Continuous (bakryEmeryBrownianNoiseReal B ω) ∧
      bakryEmeryBrownianNoiseReal B ω 0=0 := by
  have hc : ∀ᵐ ω ∂P, ∀ i, Continuous (fun t => B i t ω) := ae_all_iff.mpr (fun i => (hB i).cont)
  have hz : ∀ᵐ ω ∂P, ∀ i, B i 0 ω=0 := ae_all_iff.mpr (fun i => (hB i).eval_zero_ae_eq_zero)
  filter_upwards [hc, hz] with ω hc hz
  constructor
  · exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun i =>
      (hc i).comp continuous_real_toNNReal))
  · apply PiLp.ext
    intro i
    simpa [bakryEmeryBrownianNoiseReal] using hz i

def bakryEmeryBrownianNoisePath (T : ℝ) (B : ι → ℝ≥0 → Ω → ℝ) (ω : Ω) :
    C(Icc 0 T, EuclideanSpace ℝ ι) :=
  ContinuousMap.mkD (fun t => bakryEmeryBrownianNoiseReal B ω t.val) 0

theorem bakryEmeryBrownianNoisePath_actual (T : ℝ) (B : ι → ℝ≥0 → Ω → ℝ)
    (P : Measure Ω) (hB : ∀ i, IsBrownianReal (B i) P) :
    ∀ᵐ ω ∂P, ∀ t : Icc 0 T,
      bakryEmeryBrownianNoisePath T B ω t = bakryEmeryBrownianNoiseReal B ω t.val := by
  filter_upwards [bakryEmeryBrownianNoiseReal_actual B P hB] with ω hω
  intro t
  have hc : Continuous (fun t : Icc 0 T => bakryEmeryBrownianNoiseReal B ω t.val) :=
    hω.1.comp continuous_subtype_val
  simp [bakryEmeryBrownianNoisePath, ContinuousMap.mkD, hc]

theorem bakryEmeryBrownianNoisePath_measurable (T : ℝ) (hT : 0 ≤ T)
    (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) :
    @Measurable Ω C(Icc 0 T, EuclideanSpace ℝ ι) _ (borel _)
      (bakryEmeryBrownianNoisePath T B) := by
  letI : Nonempty (Icc 0 T) := ⟨⟨0, ⟨le_rfl, hT⟩⟩⟩
  letI : MeasurableSpace C(Icc 0 T, EuclideanSpace ℝ ι) := borel _
  letI : BorelSpace C(Icc 0 T, EuclideanSpace ℝ ι) := ⟨rfl⟩
  apply ginibre_measurable_continuousMap_of_evaluations
  intro t
  apply (aemeasurable_iff_measurable (μ := P)).mp
  have hr : Measurable (fun ω => bakryEmeryBrownianNoiseReal B ω t.val) := by
    apply (PiLp.continuous_toLp 2 _).measurable.comp
    apply measurable_pi_lambda
    intro i
    exact aemeasurable_iff_measurable.mp ((hB i).aemeasurable t.val.toNNReal)
  apply hr.aemeasurable.congr
  filter_upwards [bakryEmeryBrownianNoisePath_actual T B P hB] with ω hω
  exact (hω t).symm

#print axioms bakryEmeryBrownianNoiseReal_actual
#print axioms bakryEmeryBrownianNoisePath_actual
#print axioms bakryEmeryBrownianNoisePath_measurable
end
end GinibrePoincare
