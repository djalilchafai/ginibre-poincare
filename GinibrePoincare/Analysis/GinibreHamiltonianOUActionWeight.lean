module

public import GinibrePoincare.Analysis.GinibreHamiltonianConfigurationOUReference

@[expose] public section

/-! The correct stationary-OU reference action is a quotient by the quadratic
Hamiltonian action. Its identification as the original SDE Radon–Nikodym law
still requires the continuous Girsanov and Itô theorems. -/
open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

local instance GinibreHamiltonianOUActionWeight_realMeasurable (n : ℕ) : MeasurableSpace C(ℝ,Configuration n) := borel _
local instance GinibreHamiltonianOUActionWeight_realBorel (n : ℕ) : BorelSpace C(ℝ,Configuration n) := ⟨rfl⟩
local instance GinibreHamiltonianOUActionWeight_compactMeasurable (n : ℕ) (T : ℝ) : MeasurableSpace C(Icc (0 : ℝ) T,Configuration n) := borel _
local instance GinibreHamiltonianOUActionWeight_compactBorel (n : ℕ) (T : ℝ) : BorelSpace C(Icc (0 : ℝ) T,Configuration n) := ⟨rfl⟩

def ginibreQuadraticGradientPathWeight (n : ℕ) (α T : ℝ) (x : ℝ → Configuration n) : ℝ :=
  Real.exp (-((n : ℝ)*configurationNormSq (x 0)+(n : ℝ)*configurationNormSq (x T))/2 +
    2*α*T - α*(∫ s in (0 : ℝ)..T, configurationNormSq (x s)))

def ginibreHamiltonianOUActionWeight (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T,Configuration n)) : ℝ :=
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  ginibreHamiltonianCompactPathWeight n α T hT x /
    ginibreQuadraticGradientPathWeight n α T (ContinuousMap.IccExtendCM x)

theorem ginibreQuadraticGradientPathWeight_reverse (n : ℕ) (α T : ℝ)
    (x : ℝ → Configuration n) :
    ginibreQuadraticGradientPathWeight n α T (fun s => x (T-s)) =
    ginibreQuadraticGradientPathWeight n α T x := by
  unfold ginibreQuadraticGradientPathWeight
  have hi := intervalIntegral.integral_comp_sub_left
    (fun s => configurationNormSq (x s)) (a := 0) (b := T) T
  simp only [sub_zero,sub_self] at hi ⊢
  rw [hi]
  congr 1
  ring

theorem ginibreQuadraticGradientPathWeight_measurable (n : ℕ) (α T : ℝ) :
    Measurable (fun x : C(ℝ,Configuration n) => ginibreQuadraticGradientPathWeight n α T x) := by
  have hnorm : Measurable (configurationNormSq : Configuration n → ℝ) :=
    (contDiff_configurationNormSq (n := n)).continuous.measurable
  have hm : Measurable (fun p : C(ℝ,Configuration n) × ℝ => configurationNormSq (p.1 p.2)) :=
    hnorm.comp continuous_eval.measurable
  have hi (s : Set ℝ) : Measurable (fun x : C(ℝ,Configuration n) => ∫ t in s, configurationNormSq (x t)) :=
    hm.stronglyMeasurable.integral_prod_right'.measurable
  have he : Measurable (fun x : C(ℝ,Configuration n) => ∫ t in (0 : ℝ)..T, configurationNormSq (x t)) := by
    unfold intervalIntegral
    exact (hi _).sub (hi _)
  have h0 : Measurable (fun x : C(ℝ,Configuration n) => configurationNormSq (x 0)) :=
    hnorm.comp (continuous_eval_const (0 : ℝ)).measurable
  have hT : Measurable (fun x : C(ℝ,Configuration n) => configurationNormSq (x T)) :=
    hnorm.comp (continuous_eval_const T).measurable
  unfold ginibreQuadraticGradientPathWeight
  exact Real.measurable_exp.comp
    (((((measurable_const.mul h0).add (measurable_const.mul hT)).neg.div_const 2).add_const _).sub
      (measurable_const.mul he))

theorem ginibreHamiltonianOUActionWeight_measurable (n : ℕ) (α T : ℝ) (hT : 0 ≤ T) :
    Measurable (ginibreHamiltonianOUActionWeight n α T hT) := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  exact (ginibreHamiltonianCompactPathWeight_measurable n α T hT).div
    ((ginibreQuadraticGradientPathWeight_measurable n α T).comp
      (ContinuousMap.IccExtendCM : C(C(Icc (0 : ℝ) T,Configuration n), C(ℝ,Configuration n))).continuous.measurable)

theorem ginibreHamiltonianOUActionWeight_reverse (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T,Configuration n)) :
    ginibreHamiltonianOUActionWeight n α T hT
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
    ginibreHamiltonianOUActionWeight n α T hT x := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  unfold ginibreHamiltonianOUActionWeight
  rw [ginibreHamiltonianCompactPathWeight_reverse]
  congr 1
  change ginibreQuadraticGradientPathWeight n α T
    (fun s => ContinuousMap.IccExtendCM (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) = _
  rw [ginibreHamiltonianCompactExtend_reverse,ginibreQuadraticGradientPathWeight_reverse]

/-- The actual stationary original-Brownian OU product law, reweighted by the
correct Hamiltonian/quadratic action quotient, is time-reversal invariant.
This is a genuine measure identity; equality with the singular-SDE law remains
a separate stochastic identification, and is not assumed here. -/
theorem ginibreHamiltonianOUActionMeasure_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (α : ℝ) (T : ℝ≥0) :
    ((ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    (ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianOUActionWeight n α (T : ℝ) T.property x)) := by
  exact invariant_measure_withDensity_of_invariant_weight _ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)).measurable
    (ginibreConfigurationOUReferenceLaw_reverse n B P hB Z hZ hind _ T) _
    (ENNReal.measurable_ofReal.comp (ginibreHamiltonianOUActionWeight_measurable n α (T : ℝ) T.property))
    (fun x => congrArg ENNReal.ofReal (ginibreHamiltonianOUActionWeight_reverse n α (T : ℝ) T.property x))

#print axioms ginibreHamiltonianOUActionMeasure_reverse
#print axioms ginibreHamiltonianOUActionWeight_measurable
#print axioms ginibreHamiltonianOUActionWeight_reverse
end
end GinibrePoincare
