module

public import GinibrePoincare.Analysis.GinibreHamiltonianSublevelPathExhaustion
public import GinibrePoincare.Analysis.GinibreHamiltonianOUActionWeight
public import GinibrePoincare.Analysis.GinibreHamiltonianInitialDensityCancellation

@[expose] public section

open Set MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section
local instance ginibreKilledOUPathMeasurable (n : ℕ) (T : ℝ) :
    MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance ginibreKilledOUPathBorel (n : ℕ) (T : ℝ) :
    BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩

def ginibreHamiltonianCompactSurvival (n : ℕ) (T R : ℝ) :
    Set C(Icc (0 : ℝ) T, Configuration n) :=
  {x | ∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R}

theorem ginibreHamiltonianCompactSurvival_isOpen (n : ℕ) (T R : ℝ) :
    IsOpen (ginibreHamiltonianCompactSurvival n T R) := by
  have hW : Continuous (ginibreWeight n) :=
    (Real.continuous_exp.comp ((contDiff_configurationNormSq (n := n)).continuous.const_mul (-(n : ℝ)))).mul
      (contDiff_vandermondeWeight n).continuous
  have hG : IsOpen (ginibreHamiltonianOUSublevelDomain n R) := isOpen_lt continuous_const hW
  simpa only [ginibreHamiltonianCompactSurvival, Set.mapsTo_univ_iff, Set.range_subset_iff] using
    (ContinuousMap.isOpen_setOfPred_mapsTo (X := Icc (0 : ℝ) T) isCompact_univ hG)

theorem ginibreHamiltonianCompactSurvival_measurableSet (n : ℕ) (T R : ℝ) :
    MeasurableSet (ginibreHamiltonianCompactSurvival n T R) :=
  (ginibreHamiltonianCompactSurvival_isOpen n T R).measurableSet

/-- Literal Hamiltonian action on the event that the whole reference path
survives the prescribed Hamiltonian sublevel. -/
def ginibreHamiltonianKilledOUActionWeight (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, Configuration n) → ℝ :=
  (ginibreHamiltonianCompactSurvival n T R).indicator
    (ginibreHamiltonianOUActionWeight n α T hT)

theorem ginibreHamiltonianKilledOUActionWeight_measurable (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T) :
    Measurable (ginibreHamiltonianKilledOUActionWeight n α T R hT) :=
  (ginibreHamiltonianOUActionWeight_measurable n α T hT).indicator
    (ginibreHamiltonianCompactSurvival_measurableSet n T R)

theorem ginibreHamiltonianKilledOUActionWeight_reverse (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T,Configuration n)) :
    ginibreHamiltonianKilledOUActionWeight n α T R hT
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
      ginibreHamiltonianKilledOUActionWeight n α T R hT x := by
  classical
  have hh := ginibreHamiltonian_compact_sublevel_survival_reverse T hT R x
  change (if (∀ t, (x.comp (ginibreHamiltonianCompactReverseTime T hT)) t ∈
    ginibreHamiltonianOUSublevelDomain n R) then _ else 0) =
    (if (∀ t, x t ∈ ginibreHamiltonianOUSublevelDomain n R) then _ else 0)
  rw [hh, ginibreHamiltonianOUActionWeight_reverse]

/-- Initial Ginibre/Gaussian interaction weighting cancels the genuine
likelihood initial factor, also off survival where both killed densities vanish. -/
theorem ginibreHamiltonianKilledOUAction_initial_cancellation (n : ℕ) (α T R : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T,Configuration n)) :
    vandermondeWeight (x ⟨0,⟨le_rfl,hT⟩⟩) *
      (ginibreHamiltonianCompactSurvival n T R).indicator
        (fun y => Real.exp (ginibreInteractionPotential n (y ⟨0,⟨le_rfl,hT⟩⟩)) *
          ginibreHamiltonianOUActionWeight n α T hT y) x =
      ginibreHamiltonianKilledOUActionWeight n α T R hT x := by
  classical
  by_cases hx : x ∈ ginibreHamiltonianCompactSurvival n T R
  · have h0 := hx (⟨0,⟨le_rfl,hT⟩⟩ : Icc (0 : ℝ) T)
    have hK : x ⟨0,⟨le_rfl,hT⟩⟩ ∈ ginibreHamiltonianSublevel n R := by
      rw [ginibreHamiltonianSublevel_eq_weight_superlevel]
      exact (show Real.exp (-R) < ginibreWeight n (x ⟨0,⟨le_rfl,hT⟩⟩) from h0).le
    simp only [Set.indicator_of_mem hx,ginibreHamiltonianKilledOUActionWeight]
    exact ginibreInteraction_initial_action_cancellation _ hK.1 _
  · simp only [Set.indicator_of_notMem hx,ginibreHamiltonianKilledOUActionWeight,mul_zero]

/-- Reversal of the actual stationary original-Brownian OU reference with the
literal killed action. Identification with the killed singular SDE is separate. -/
theorem ginibreHamiltonianKilledOUActionMeasure_reverse {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (hB : IsBrownianReal B P) (Z : Ω → ℝ) (hZ : HasLaw Z (gaussianReal 0 (1/2)) P)
    (hind : IndepFun Z (fun ω t => B t ω) P) (α R : ℝ) (T : ℝ≥0) :
    ((ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)) =
    (ginibreConfigurationOUReferenceLaw n B P Z (2*α/(n : ℝ)).toNNReal T).withDensity
      (fun x => ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight n α (T : ℝ) R T.property x)) := by
  exact invariant_measure_withDensity_of_invariant_weight _ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime (T : ℝ) T.property)).measurable
    (ginibreConfigurationOUReferenceLaw_reverse n B P hB Z hZ hind _ T) _
    (ENNReal.measurable_ofReal.comp (ginibreHamiltonianKilledOUActionWeight_measurable n α (T : ℝ) R T.property))
    (fun x => congrArg ENNReal.ofReal (ginibreHamiltonianKilledOUActionWeight_reverse n α (T : ℝ) R T.property x))

#print axioms ginibreHamiltonianKilledOUAction_initial_cancellation
#print axioms ginibreHamiltonianCompactSurvival_measurableSet
#print axioms ginibreHamiltonianKilledOUActionMeasure_reverse
end
end GinibrePoincare
