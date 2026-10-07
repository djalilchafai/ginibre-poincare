module

public import GinibrePoincare.Analysis.MatrixSpectralSobolevRealSplit
public import GinibrePoincare.Analysis.MatrixSpectralSobolevCandidateLines
public import GinibrePoincare.Analysis.MatrixSpectralSobolevFubini

@[expose] public section

/-! # Ordinary distributional identities across actual polynomial collisions -/
open MeasureTheory Filter MvPolynomial
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem polynomial_collision_real_first_slices (d : ℕ)
    (p : MvPolynomial (Fin (d + 1)) ℂ) (hp : p ≠ 0)
    (F : Configuration (d + 1) → ℝ) (hF : Continuous F)
    (hd : ∀ z, MvPolynomial.eval z p ≠ 0 → DifferentiableAt ℝ F z)
    (hg : LocallyIntegrable
      (fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) volume) :
    ∀ᵐ y ∂(volume : Measure (ℝ × Configuration d)),
      Continuous (fun t => F (configurationRealFirstSplit d (t, y))) ∧
      LocallyIntegrable
        (fun t => fderiv ℝ F (configurationRealFirstSplit d (t, y)) (Fin.cons (1 : ℂ) 0))
        volume ∧
      ∃ S : Finset ℝ, ∀ t, t ∉ S →
        HasDerivAt (fun s => F (configurationRealFirstSplit d (s, y)))
          (fderiv ℝ F (configurationRealFirstSplit d (t, y)) (Fin.cons (1 : ℂ) 0)) t := by
  classical
  have hcross := complexMvPolynomial_real_line_crossings_finite_ae d p hp
  have hx : ∀ᵐ y ∂(volume : Measure (ℝ × Configuration d)),
      ∀ c v : ℂ, v ≠ 0 →
        {t : ℝ | eval (Fin.cons (c + (t : ℂ) * v) y.2) p = 0}.Finite := by
    exact Measure.quasiMeasurePreserving_snd.ae hcross
  have hloc := locallyIntegrable_real_product_slices
    (volume : Measure (ℝ × Configuration d))
    ((fun z => fderiv ℝ F z (Fin.cons (1 : ℂ) 0)) ∘ configurationRealFirstSplit d)
    (configurationRealFirstSplit_locallyIntegrable d _ hg)
  filter_upwards [hx, hloc] with y hy hgy
  refine ⟨hF.comp (by fun_prop), hgy, ?_⟩
  let S : Finset ℝ := (hy ((y.1 : ℂ) * Complex.I) 1 one_ne_zero).toFinset
  refine ⟨S, ?_⟩
  intro t ht
  have hz : eval (configurationRealFirstSplit d (t, y)) p ≠ 0 := by
    have h := ht
    simp only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h
    have heq : configurationRealFirstSplit d (t, y) =
        Fin.cons ((y.1 : ℂ) * Complex.I + (t : ℂ) * 1) y.2 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · apply Complex.ext <;> change _ = _ <;> simp [configurationRealFirstSplit]
      · rfl
    rw [heq]
    exact h
  have hl := configurationRealFirstSplit_line_hasDerivAt d y t
  exact (hd _ hz).hasFDerivAt.comp_hasDerivAt t hl

end
end GinibrePoincare
