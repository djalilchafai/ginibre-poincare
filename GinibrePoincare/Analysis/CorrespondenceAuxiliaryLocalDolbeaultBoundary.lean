module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultHomotopy
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultIteration

@[expose] public section
open MeasureTheory Set Filter
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem planarDbar_contDiff_infty (χ : ℂ → ℂ) (hχ : ContDiff ℝ ∞ χ) :
    ContDiff ℝ ∞ (planarDbar χ) := finiteComplexDbar_contDiff χ hχ 1 Complex.I

theorem planarDbar_tsupport_subset (χ : ℂ → ℂ) : tsupport (planarDbar χ) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro z hz
  by_contra h
  apply hz
  change planarDbar χ z = 0
  simp [planarDbar, fderiv_of_notMem_tsupport ℝ h]

def configurationCauchyGreenBoundary {n : ℕ} (j : Fin n) (χ : ℂ → ℂ)
    (a : Configuration n → ℂ) : Configuration n → ℂ :=
  configurationCauchyGreenPotential j (planarDbar χ) a

theorem configurationCauchyGreenBoundary_contDiff {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (configurationCauchyGreenBoundary j χ a) :=
  configurationCauchyGreenPotential_contDiff j _ a (planarDbar_contDiff_infty χ hχ)
    (planarDbar_compact χ hc) ha

theorem configurationCauchyGreenPotential_congr_on_support {n : ℕ} (j : Fin n)
    (χ : ℂ → ℂ) (a b : Configuration n → ℂ) (p : Configuration n)
    (he : ∀ z ∈ tsupport χ, a (dolbeaultReplaceCoordinate j (p, z)) =
      b (dolbeaultReplaceCoordinate j (p, z))) :
    configurationCauchyGreenPotential j χ a p = configurationCauchyGreenPotential j χ b p := by
  change (∫ y : ℂ, cauchyGreenKernel y *
      (χ (p j-y)*a (dolbeaultReplaceCoordinate j (p, p j-y)))) =
    ∫ y : ℂ, cauchyGreenKernel y * (χ (p j-y)*b (dolbeaultReplaceCoordinate j (p, p j-y)))
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun y => by
    change cauchyGreenKernel y * (χ (p j-y)*a (dolbeaultReplaceCoordinate j (p, p j-y))) =
      cauchyGreenKernel y * (χ (p j-y)*b (dolbeaultReplaceCoordinate j (p, p j-y)))
    by_cases hy : p j-y ∈ tsupport χ
    · rw [he _ hy]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, zero_mul])

theorem dolbeaultCylinder_replace {n : ℕ} (W V : Fin n → Set ℂ)
    (s : Finset (Fin n)) (j : Fin n) (hjs : j ∉ s) (p : Configuration n)
    (hp : p ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s)
    (z : ℂ) (hz : z ∈ W j) :
    dolbeaultReplaceCoordinate j (p, z) ∈ dolbeaultCylinder W Finset.univ ∩ dolbeaultCylinder V s := by
  constructor
  · intro k _
    by_cases hk : k = j
    · subst k; simpa [dolbeaultReplaceCoordinate_apply] using hz
    · simpa only [dolbeaultReplaceCoordinate_apply, if_neg hk] using hp.1 k (Finset.mem_univ k)
  · intro k hk
    have hkj : k ≠ j := by intro he; subst k; exact hjs hk
    simpa only [dolbeaultReplaceCoordinate_apply, if_neg hkj] using hp.2 k hk

def smoothDolbeaultBoundaryComposition {n : ℕ} (χ : Fin n → ℂ → ℂ) :
    List (Fin n) → (Configuration n → ℂ) → Configuration n → ℂ
  | [], a => a
  | j::l, a => configurationCauchyGreenBoundary j (χ j) (smoothDolbeaultBoundaryComposition χ l a)

def smoothDolbeaultPrimitive {n : ℕ} (χ : Fin n → ℂ → ℂ)
    (α : Fin n → Configuration n → ℂ) : List (Fin n) → Configuration n → ℂ
  | [] => 0
  | j::l => smoothDolbeaultPrimitive χ α l + configurationCauchyGreenPotential j (χ j)
      (smoothDolbeaultBoundaryComposition χ l (α j))

theorem smoothDolbeaultBoundaryComposition_contDiff {n : ℕ} (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (l : List (Fin n)) (a : Configuration n → ℂ) (ha : ContDiff ℝ ∞ a) :
    ContDiff ℝ ∞ (smoothDolbeaultBoundaryComposition χ l a) := by
  induction l with
  | nil => exact ha
  | cons j l ih => exact configurationCauchyGreenBoundary_contDiff j _ _ (hχ j) (hc j) ih

theorem smoothDolbeaultPrimitive_contDiff {n : ℕ} (χ : Fin n → ℂ → ℂ)
    (hχ : ∀ j, ContDiff ℝ ∞ (χ j)) (hc : ∀ j, HasCompactSupport (χ j))
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, ContDiff ℝ ∞ (α j))
    (l : List (Fin n)) : ContDiff ℝ ∞ (smoothDolbeaultPrimitive χ α l) := by
  induction l with
  | nil => exact contDiff_const
  | cons j l ih => exact ih.add (configurationCauchyGreenPotential_contDiff j _ _
      (hχ j) (hc j) (smoothDolbeaultBoundaryComposition_contDiff χ hχ hc l _ (hα j)))

#print axioms planarDbar_contDiff_infty
#print axioms planarDbar_tsupport_subset
#print axioms configurationCauchyGreenBoundary_contDiff
#print axioms configurationCauchyGreenPotential_congr_on_support
#print axioms dolbeaultCylinder_replace
#print axioms smoothDolbeaultBoundaryComposition_contDiff
#print axioms smoothDolbeaultPrimitive_contDiff
end
end GinibrePoincare
