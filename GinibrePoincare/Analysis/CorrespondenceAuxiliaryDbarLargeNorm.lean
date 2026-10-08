module

public import GinibrePoincare.Analysis.GaussianCanonicalDbarSolution

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- Holomorphic addition allows solutions of a fixed Gaussian dbar equation
to have arbitrarily large norm, the additional assertion in Remark 2.4. -/
theorem gaussianSchwartzDbar_solutions_unbounded_norm {n : ℕ} (hn : 0 < n)
    (u : Lp ℂ 2 (complexGaussianMeasure n))
    (D : Fin n → Lp ℂ 2 (complexGaussianMeasure n))
    (hu : ∀ j, IsGaussianSchwartzDbar n u (D j) j) (B : ℝ) :
    ∃ v : Lp ℂ 2 (complexGaussianMeasure n),
      (∀ j, IsGaussianSchwartzDbar n v (D j) j) ∧ B < ‖v‖ := by
  let c : ℂ := (‖u‖+|B|+1 : ℝ)
  let k : Lp ℂ 2 (complexGaussianMeasure n) := Lp.const 2 (complexGaussianMeasure n) c
  have hk : k ∈ gaussianEntireL2 n := by
    refine ⟨fun _ => c,?_,?_⟩
    · exact fun z => differentiableAt_const c
    · exact (Lp.coeFn_const 2 (complexGaussianMeasure n) c).symm
  refine ⟨u-k,?_,?_⟩
  · intro j
    apply (gaussianSchwartzDbar_iff_weak hn _ _ j).mpr
    simpa only [sub_zero] using gaussianWeakDbar_subtract hn u (D j) k 0 j
      ((gaussianSchwartzDbar_iff_weak hn _ _ j).mp (hu j))
      (gaussianEntireL2_weakDbar_zero hn k hk j)
  · have hkn : ‖k‖ = ‖u‖+|B|+1 := by
      rw [Lp.norm_const 2 (complexGaussianMeasure n) c (by norm_num)]
      have hcNorm : ‖c‖ = ‖u‖+|B|+1 := by
        change ‖((‖u‖+|B|+1 : ℝ) : ℂ)‖ = _
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
      simp only [hcNorm]
      simp
    have hbound := norm_sub_norm_le k u
    rw [norm_sub_rev] at hbound
    rw [hkn] at hbound
    linarith [le_abs_self B]

#print axioms gaussianSchwartzDbar_solutions_unbounded_norm
end
end GinibrePoincare
