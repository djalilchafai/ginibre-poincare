module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultBoundaryIteration
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMultiplierComposition

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem dolbeault_compact_continuous_bound (χ : ℂ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) : ∃ C : ℝ, ∀ z, ‖χ z‖ ≤ C := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hχ.continuousOn
  refine ⟨max C 0, fun z => ?_⟩
  by_cases hz : z ∈ tsupport χ
  · exact (hC z hz).trans (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
    exact le_max_right _ _

def dolbeaultCompactBound (χ : ℂ → ℂ) (hχ : Continuous χ) (hc : HasCompactSupport χ) : ℝ :=
  Classical.choose (dolbeault_compact_continuous_bound χ hχ hc)

theorem dolbeaultCompactBound_spec (χ : ℂ → ℂ) (hχ : Continuous χ)
    (hc : HasCompactSupport χ) (z : ℂ) : ‖χ z‖ ≤ dolbeaultCompactBound χ hχ hc :=
  Classical.choose_spec (dolbeault_compact_continuous_bound χ hχ hc) z

def dolbeaultCutoffLpMultiplier {n : ℕ} (j : Fin n) (χ : ℂ → ℂ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  dolbeaultBoundedMultiplier (fun p => χ (p j))
    ((hχ.comp (continuous_apply j)).aestronglyMeasurable)
    (dolbeaultCompactBound χ hχ hc) (ae_of_all _ (fun p => dolbeaultCompactBound_spec χ hχ hc (p j)))

def dolbeaultCutoffLpOperator {n : ℕ} (j : Fin n) (R : ℝ) (χ : ℂ → ℂ)
    (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  (dolbeaultCauchyGreenL2 j R).comp (dolbeaultCutoffLpMultiplier j χ hχ hc)

def dolbeaultBoundaryLpOperator {n : ℕ} (j : Fin n) (R : ℝ) (χ : ℂ → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) :
    dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n :=
  dolbeaultCutoffLpOperator j R (planarDbar χ)
    (planarDbar_contDiff_infty χ hχ).continuous (planarDbar_compact χ hc)

def dolbeaultBoundaryLpComposition {n : ℕ} (R : ℝ) (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j)) :
    List (Fin n) → dolbeaultOrdinaryL2 n →L[ℂ] dolbeaultOrdinaryL2 n
  | [] => ContinuousLinearMap.id ℂ _
  | j::l => (dolbeaultBoundaryLpOperator j R (χ j) (hχ j) (hc j)).comp
      (dolbeaultBoundaryLpComposition R χ hχ hc l)

def dolbeaultPrimitiveLp {n : ℕ} (R : ℝ) (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (α : Fin n → dolbeaultOrdinaryL2 n) : List (Fin n) → dolbeaultOrdinaryL2 n
  | [] => 0
  | j::l => dolbeaultPrimitiveLp R χ hχ hc α l +
      dolbeaultCutoffLpOperator j R (χ j) (hχ j).continuous (hc j)
        (dolbeaultBoundaryLpComposition R χ hχ hc l (α j))

/-- Strong ordinary L² convergence survives the actual finite homotopy,
with every cutoff and kernel operator constructed internally. -/
theorem dolbeaultPrimitiveLp_tendsto {n : ℕ} {ι : Type*} {f : Filter ι}
    (R : ℝ) (χ : Fin n → ℂ → ℂ) (hχ : ∀ j, ContDiff ℝ ∞ (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (α : ι → Fin n → dolbeaultOrdinaryL2 n) (a : Fin n → dolbeaultOrdinaryL2 n)
    (ha : ∀ j, Tendsto (fun i => α i j) f (𝓝 (a j))) (l : List (Fin n)) :
    Tendsto (fun i => dolbeaultPrimitiveLp R χ hχ hc (α i) l) f
      (𝓝 (dolbeaultPrimitiveLp R χ hχ hc a l)) := by
  induction l with
  | nil => exact tendsto_const_nhds
  | cons j l ih =>
    exact ih.add (((dolbeaultCutoffLpOperator j R (χ j) (hχ j).continuous (hc j)).continuous.comp
      (dolbeaultBoundaryLpComposition R χ hχ hc l).continuous).continuousAt.tendsto.comp (ha j))

#print axioms dolbeault_compact_continuous_bound
#print axioms dolbeaultCompactBound_spec
#print axioms dolbeaultCutoffLpMultiplier
#print axioms dolbeaultCutoffLpOperator
#print axioms dolbeaultBoundaryLpOperator
#print axioms dolbeaultPrimitiveLp_tendsto
end
end GinibrePoincare
