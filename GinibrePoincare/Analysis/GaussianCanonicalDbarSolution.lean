module

public import GinibrePoincare.Analysis.GaussianEntireSpaceClosure
public import GinibrePoincare.Analysis.GaussianClosedFormVolume

@[expose] public section

/-! # The canonical minimum norm solution of the Gaussian ∂bar equation -/
open MeasureTheory
open scoped BigOperators
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

def gaussianCanonicalDbarSolution {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) : Lp ℂ 2 (complexGaussianMeasure n) :=
  u - (gaussianEntireClosedSpace n hn).starProjection u

theorem gaussianWeakDbar_subtract {n : ℕ} (hn : 0 < n)
    (u D v E : Lp ℂ 2 (complexGaussianMeasure n)) (j : Fin n)
    (hu : IsGaussianWeakDbar n u D j) (hv : IsGaussianWeakDbar n v E j) :
    IsGaussianWeakDbar n (u - v) (D - E) j := by
  apply gaussianWeakDbar_of_hermiteCoefficient hn
  intro pq
  have hcu := gaussianWeakDbar_hermiteCoefficient hn u D j hu pq
  have hcv := gaussianWeakDbar_hermiteCoefficient hn v E j hv pq
  simp only [gaussianHermiteCoefficient, map_sub, lp.coeFn_sub, Pi.sub_apply] at hcu hcv ⊢
  rw [hcu, hcv]
  ring

theorem gaussianEntireL2_weakDbar_zero {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n)) (hu : u ∈ gaussianEntireL2 n)
    (j : Fin n) : IsGaussianWeakDbar n u 0 j := by
  obtain ⟨f, hf⟩ := hu
  apply gaussian_smooth_weak_dbar hn j u 0 f
    (gaussian_entire_contDiff_real_one hf.1) hf.2.symm
  filter_upwards [Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hz
  rw [hz, dbarComponent_eq_zero_of_differentiable_complex hf.1]
  rfl

/-- Removing the projection onto the actual entire kernel preserves all
ordinary distributional derivatives. -/
theorem gaussianCanonicalDbarSolution_schwartz {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) :
    ∀ j, IsGaussianSchwartzDbar n (gaussianCanonicalDbarSolution hn u) (D j) j := by
  intro j
  apply (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr
  have hP := gaussianEntireL2_weakDbar_zero hn _
    (Submodule.starProjection_apply_mem (gaussianEntireClosedSpace n hn).toSubmodule u) j
  simpa only [sub_zero, gaussianCanonicalDbarSolution] using gaussianWeakDbar_subtract hn u (D j)
    ((gaussianEntireClosedSpace n hn).starProjection u) 0 j
    ((gaussianSchwartzDbar_iff_weak hn u (D j) j).mp (hu j)) hP

theorem gaussianCanonicalDbarSolution_norm_sq_le {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) :
    ‖gaussianCanonicalDbarSolution hn u‖ ^ 2 ≤
      (1 / (n : ℝ)) * ∑ j, ‖D j‖ ^ 2 :=
  gaussianSchwartzDbar_entire_gap hn u D hu

/-- Every competing solution differs from the canonical solution by an
actual entire function and satisfies the exact Pythagorean norm identity. -/
theorem gaussianCanonicalDbarSolution_pythagoras {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j)
    (hv : ∀ j, IsGaussianSchwartzDbar n v (D j) j) :
    v - gaussianCanonicalDbarSolution hn u ∈ gaussianEntireL2 n ∧
      ‖v‖ ^ 2 = ‖gaussianCanonicalDbarSolution hn u‖ ^ 2 +
        ‖v - gaussianCanonicalDbarSolution hn u‖ ^ 2 := by
  have hcan := gaussianCanonicalDbarSolution_schwartz hn u D hu
  have hk : ∀ j, IsGaussianWeakDbar n (v - gaussianCanonicalDbarSolution hn u) 0 j := by
    intro j
    simpa only [sub_self] using gaussianWeakDbar_subtract hn v (D j)
      (gaussianCanonicalDbarSolution hn u) (D j) j
      ((gaussianSchwartzDbar_iff_weak hn _ _ j).mp (hv j))
      ((gaussianSchwartzDbar_iff_weak hn _ _ j).mp (hcan j))
  have hmem : v - gaussianCanonicalDbarSolution hn u ∈ gaussianEntireL2 n :=
    gaussianWeakHolomorphic_has_entire_representative hn _ hk
  refine ⟨hmem, ?_⟩
  have ho := Submodule.starProjection_inner_eq_zero (K := (gaussianEntireClosedSpace n hn).toSubmodule) u
    (v - gaussianCanonicalDbarSolution hn u) hmem
  have hnrm := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (gaussianCanonicalDbarSolution hn u) (v - gaussianCanonicalDbarSolution hn u) ho
  rw [add_sub_cancel] at hnrm
  simpa only [pow_two] using hnrm

theorem gaussianCanonicalDbarSolution_minimal {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j)
    (hv : ∀ j, IsGaussianSchwartzDbar n v (D j) j) :
    ‖gaussianCanonicalDbarSolution hn u‖ ≤ ‖v‖ := by
  have h := (gaussianCanonicalDbarSolution_pythagoras hn u v D hu hv).2
  nlinarith [sq_nonneg ‖v - gaussianCanonicalDbarSolution hn u‖,
    norm_nonneg v, norm_nonneg (gaussianCanonicalDbarSolution hn u)]

theorem gaussianCanonicalDbarSolution_minimal_eq_iff {n : ℕ} (hn : 0 < n)
    (u v : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j)
    (hv : ∀ j, IsGaussianSchwartzDbar n v (D j) j) :
    ‖gaussianCanonicalDbarSolution hn u‖ = ‖v‖ ↔ gaussianCanonicalDbarSolution hn u = v := by
  constructor
  · intro heq
    have hp := (gaussianCanonicalDbarSolution_pythagoras hn u v D hu hv).2
    rw [heq] at hp
    have hz : ‖v - gaussianCanonicalDbarSolution hn u‖ = 0 := by
      nlinarith [norm_nonneg (v - gaussianCanonicalDbarSolution hn u)]
    exact (sub_eq_zero.mp (norm_eq_zero.mp hz)).symm
  · intro heq; rw [heq]

/-- Remark 2.4 with its canonical interpretation: every actual ordinary
distributionally closed square-integrable form has a unique minimum norm
solution, with the paper's exact sharp norm estimate. -/
theorem gaussianVolumeClosedForm_canonicalSolvability {n : ℕ} (hn : 0 < n)
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hD : IsGaussianVolumeClosedForm n D) :
    ∃ u : Lp ℂ 2 (complexGaussianMeasure n),
      (∀ j, IsGaussianSchwartzDbar n u (D j) j) ∧
      ‖u‖ ^ 2 ≤ (1 / (n : ℝ)) * ∑ j, ‖D j‖ ^ 2 ∧
      ∀ v : Lp ℂ 2 (complexGaussianMeasure n),
        (∀ j, IsGaussianSchwartzDbar n v (D j) j) →
        ‖u‖ ≤ ‖v‖ ∧ (‖u‖ = ‖v‖ ↔ u = v) := by
  obtain ⟨w, _, hw⟩ := gaussianVolumeClosedFormSolvability hn D hD
  have hws : ∀ j, IsGaussianSchwartzDbar n w (D j) j := by
    intro j
    exact (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr
      (gaussianVolumeDistributionalDbar_weak hn _ _ j (hw j))
  refine ⟨gaussianCanonicalDbarSolution hn w,
    gaussianCanonicalDbarSolution_schwartz hn w D hws,
    gaussianCanonicalDbarSolution_norm_sq_le hn w D hws, ?_⟩
  intro v hv
  exact ⟨gaussianCanonicalDbarSolution_minimal hn w v D hws hv,
    gaussianCanonicalDbarSolution_minimal_eq_iff hn w v D hws hv⟩

#print axioms gaussianCanonicalDbarSolution_schwartz
#print axioms gaussianCanonicalDbarSolution_norm_sq_le
#print axioms gaussianCanonicalDbarSolution_pythagoras
#print axioms gaussianCanonicalDbarSolution_minimal
#print axioms gaussianVolumeClosedForm_canonicalSolvability

end
end GinibrePoincare
