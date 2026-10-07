module

public import GinibrePoincare.Analysis.MatrixSchurSortedDecomposition
public import GinibrePoincare.Analysis.MatrixSchurGaussianIntegration

@[expose] public section

open Matrix NormedSpace MeasureTheory Filter Set Order
open scoped Matrix Matrix.Norms.Operator Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 10000

theorem measurableSet_matrixSchurOrderedDiagonal (n : ℕ) :
    MeasurableSet {A : Matrix (Fin n) (Fin n) ℂ | matrixSchurOrderedDiagonal A} := by
  change MeasurableSet {A : Fin n → Fin n → ℂ |
    ∀ i j : Fin n, i < j → toLex ((A i i).re, (A i i).im) < toLex ((A j j).re, (A j j).im)}
  simp only [setOf_forall]
  apply MeasurableSet.iInter
  intro i
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i < j
  · simp only [hij, iInter_true, Prod.Lex.toLex_lt_toLex]
    have hir : Measurable (fun A : Fin n → Fin n → ℂ => (A i i).re) := by fun_prop
    have hjr : Measurable (fun A : Fin n → Fin n → ℂ => (A j j).re) := by fun_prop
    have hii : Measurable (fun A : Fin n → Fin n → ℂ => (A i i).im) := by fun_prop
    have hji : Measurable (fun A : Fin n → Fin n → ℂ => (A j j).im) := by fun_prop
    exact (measurableSet_lt hir hjr).union ((measurableSet_eq_fun hir hjr).inter
      (measurableSet_lt hii hji))
  · simp [hij]

def matrixSchurSortedUpperDomain (n : ℕ) : Set (SchurUpperIndex n → ℂ) :=
  {y | matrixSchurOrderedDiagonal (schurUpperCombination y)}

theorem measurableSet_matrixSchurSortedUpperDomain (n : ℕ) :
    MeasurableSet (matrixSchurSortedUpperDomain n) := by
  letI : BorelSpace (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (BorelSpace (Fin n → Fin n → ℂ))
  have hc : Measurable (schurUpperCombination (n := n)) := by
    have he : (schurUpperCombination (n := n)) = schurUpperCLM n :=
      funext fun y => (schurUpperCLM_apply n y).symm
    rw [he]
    exact (schurUpperCLM n).continuous.measurable
  exact hc (measurableSet_matrixSchurOrderedDiagonal n)

theorem schurUpperCombination_injective (n : ℕ) :
    Function.Injective (schurUpperCombination (n := n)) := by
  intro y z he
  funext p
  have hp := congrArg (fun A : Matrix (Fin n) (Fin n) ℂ => A p.val.1 p.val.2) he
  simpa only [schurUpperCombination_entry] using hp

/-- A single open angular neighborhood gives an injective Schur chart with all
ordered eigenvalues and all strict upper entries, including unbounded ones. -/
theorem matrixSchurSortedDomain_exists_injective (n : ℕ) :
    ∃ V : Set (SchurLowerIndex n → ℂ), IsOpen V ∧ 0 ∈ V ∧
      InjOn (matrixSchurFrameChart (matrixSchurExponentialFrame n) (0 : Matrix (Fin n) (Fin n) ℂ))
        (V ×ˢ matrixSchurSortedUpperDomain n) := by
  obtain ⟨N, hN, hslice⟩ := matrixSchur_uniform_sorted_slice n
  obtain ⟨V, hVN, hV, h0⟩ := mem_nhds_iff.mp hN
  refine ⟨V, hV, h0, ?_⟩
  rintro p hp q hq he
  have hx := hslice p.1 (hVN hp.1) q.1 (hVN hq.1)
    (schurUpperCombination p.2) (schurUpperCombination q.2)
    (fun i j hij => schurUpperCombination_lower_zero _ i j hij)
    (fun i j hij => schurUpperCombination_lower_zero _ i j hij) hp.2 hq.2
  have he' : matrixSchurExponentialFrame n p.1 * schurUpperCombination p.2 *
      (matrixSchurExponentialFrame n p.1)ᴴ =
    matrixSchurExponentialFrame n q.1 * schurUpperCombination q.2 *
      (matrixSchurExponentialFrame n q.1)ᴴ := by
    simpa only [matrixSchurFrameChart, zero_add] using he
  obtain ⟨hfirst, hsecond⟩ := hx he'
  exact Prod.ext hfirst (schurUpperCombination_injective n hsecond)

#print axioms matrixSchurSortedDomain_exists_injective
end
end GinibrePoincare
