module

public import GinibrePoincare.Analysis.GinibreHamiltonianGradientPathMeasure
public import Mathlib.Topology.ContinuousMap.Interval

@[expose] public section

/-! Genuine Borel Hamiltonian action on compact-horizon continuous paths. -/
open Set MeasureTheory
namespace GinibrePoincare
noncomputable section

local instance GinibreHamiltonianCompactPathWeight_instance1 (n : ℕ) (T : ℝ) : MeasurableSpace C(Icc (0 : ℝ) T, Configuration n) := borel _
local instance GinibreHamiltonianCompactPathWeight_instance2 (n : ℕ) (T : ℝ) : BorelSpace C(Icc (0 : ℝ) T, Configuration n) := ⟨rfl⟩
local instance GinibreHamiltonianCompactPathWeight_instance3 (n : ℕ) : MeasurableSpace C(ℝ, Configuration n) := borel _
local instance GinibreHamiltonianCompactPathWeight_instance4 (n : ℕ) : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩

/-- The compact-horizon action uses the actual endpoint values and time integral;
`IccExtendCM` only supplies the values outside the integration interval. -/
def ginibreHamiltonianCompactPathWeight (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) : ℝ :=
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  ginibreHamiltonianGradientPathWeight n α T (ContinuousMap.IccExtendCM x)

theorem ginibreHamiltonianCompactPathWeight_measurable (n : ℕ) (α T : ℝ) (hT : 0 ≤ T) :
    Measurable (ginibreHamiltonianCompactPathWeight n α T hT) := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  exact (ginibreHamiltonianGradientPathWeight_measurable n α T).comp
    (ContinuousMap.IccExtendCM : C(C(Icc (0 : ℝ) T, Configuration n), C(ℝ, Configuration n))).continuous.measurable

def ginibreHamiltonianCompactReverseTime (T : ℝ) (hT : 0 ≤ T) :
    C(Icc (0 : ℝ) T, Icc (0 : ℝ) T) :=
  ⟨fun t => ⟨T-t.val, by constructor <;> linarith [t.property.1, t.property.2]⟩,
    by fun_prop⟩

theorem ginibreHamiltonianCompactExtend_reverse (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    (letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
    (fun s => ContinuousMap.IccExtendCM
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) =
      (fun s => ContinuousMap.IccExtendCM x (T-s))) := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  have hclamp (s : ℝ) : max 0 (min T (T-s)) = T - max 0 (min T s) := by
    by_cases hs : s ≤ 0
    · have hTs : T ≤ T-s := by linarith
      simp [min_eq_left hTs, min_eq_right (hs.trans hT), max_eq_left hs,
        max_eq_right hT]
    · have hs0 : 0 ≤ s := le_of_lt (lt_of_not_ge hs)
      by_cases hsT : s ≤ T
      · have ht0 : 0 ≤ T-s := by linarith
        have htT : T-s ≤ T := by linarith
        simp [min_eq_right hsT, max_eq_right hs0, min_eq_right htT, max_eq_right ht0]
      · have hTs0 : T-s ≤ 0 := by linarith
        simp [min_eq_left (le_of_lt (lt_of_not_ge hsT)), max_eq_right hT,
          min_eq_right (hTs0.trans hT), max_eq_left hTs0]
  have he : (fun s => ContinuousMap.IccExtendCM
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) =
      (fun s => ContinuousMap.IccExtendCM x (T-s)) := by
    funext s
    change x (ginibreHamiltonianCompactReverseTime T hT (projIcc 0 T hT s)) =
      x (projIcc 0 T hT (T-s))
    congr 1
    apply Subtype.ext
    exact (hclamp s).symm
  exact he

theorem ginibreHamiltonianCompactPathWeight_reverse (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (x : C(Icc (0 : ℝ) T, Configuration n)) :
    ginibreHamiltonianCompactPathWeight n α T hT
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
    ginibreHamiltonianCompactPathWeight n α T hT x := by
  letI : Fact ((0 : ℝ) ≤ T) := ⟨hT⟩
  have hclamp (s : ℝ) : max 0 (min T (T-s)) = T - max 0 (min T s) := by
    by_cases hs : s ≤ 0
    · have hTs : T ≤ T-s := by linarith
      simp [min_eq_left hTs, min_eq_right (hs.trans hT), max_eq_left hs,
        max_eq_right hT]
    · have hs0 : 0 ≤ s := le_of_lt (lt_of_not_ge hs)
      by_cases hsT : s ≤ T
      · have ht0 : 0 ≤ T-s := by linarith
        have htT : T-s ≤ T := by linarith
        simp [min_eq_right hsT, max_eq_right hs0, min_eq_right htT, max_eq_right ht0]
      · have hTs0 : T-s ≤ 0 := by linarith
        simp [min_eq_left (le_of_lt (lt_of_not_ge hsT)), max_eq_right hT,
          min_eq_right (hTs0.trans hT), max_eq_left hTs0]
  have he : (fun s => ContinuousMap.IccExtendCM
      (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) =
      (fun s => ContinuousMap.IccExtendCM x (T-s)) := by
    funext s
    change x (ginibreHamiltonianCompactReverseTime T hT (projIcc 0 T hT s)) =
      x (projIcc 0 T hT (T-s))
    congr 1
    apply Subtype.ext
    exact (hclamp s).symm
  unfold ginibreHamiltonianCompactPathWeight
  change ginibreHamiltonianGradientPathWeight n α T
    (fun s => ContinuousMap.IccExtendCM (x.comp (ginibreHamiltonianCompactReverseTime T hT)) s) = _
  rw [he, ginibreHamiltonianGradientPathWeight_reverse]

/-- Reweighting a reversible reference path measure by the actual compact
Hamiltonian action preserves its reversal law. This does not identify the
weighted law with the original Brownian singular diffusion. -/
theorem ginibreHamiltonianCompactPathMeasure_reverse (n : ℕ) (α T : ℝ) (hT : 0 ≤ T)
    (μ : Measure C(Icc (0 : ℝ) T, Configuration n))
    (hμ : μ.map (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT)) = μ) :
    (μ.withDensity (fun x => ENNReal.ofReal (ginibreHamiltonianCompactPathWeight n α T hT x))).map
      (fun x => x.comp (ginibreHamiltonianCompactReverseTime T hT)) =
    μ.withDensity (fun x => ENNReal.ofReal (ginibreHamiltonianCompactPathWeight n α T hT x)) := by
  exact invariant_measure_withDensity_of_invariant_weight μ _
    (ContinuousMap.continuous_precomp (ginibreHamiltonianCompactReverseTime T hT)).measurable hμ _
    (ENNReal.measurable_ofReal.comp (ginibreHamiltonianCompactPathWeight_measurable n α T hT))
    (fun x => congrArg ENNReal.ofReal (ginibreHamiltonianCompactPathWeight_reverse n α T hT x))

#print axioms ginibreHamiltonianCompactPathMeasure_reverse
#print axioms ginibreHamiltonianCompactPathWeight_reverse
#print axioms ginibreHamiltonianCompactPathWeight_measurable
end
end GinibrePoincare
