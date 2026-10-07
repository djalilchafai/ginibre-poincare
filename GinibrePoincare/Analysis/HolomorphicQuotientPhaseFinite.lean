module

public import GinibrePoincare.Analysis.GaussianHolomorphicPhasePolynomial
public import GinibrePoincare.Analysis.GaussianVandermondePhase
public import GinibrePoincare.Analysis.GinibreConjugationGeometry

@[expose] public section

/-! # Finite reconstruction of actual closed homogeneous quotient vectors -/
open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
open ComplexHermite
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem finiteZeroHermiteL2_alternating_polynomial {n : ℕ} (hn : 0 < n)
    (S : Finset (Fin n → ℕ)) (c : (Fin n → ℕ) → ℂ)
    (hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n) :
    IsAlternatingConfigurationPolynomial (finiteZeroAntiholomorphicHermitePolynomial n S c) := by
  apply (finiteHermiteSum_isAlternating_iff hn S c).1
  intro σ
  have heq : (fun z ↦ finiteZeroAntiholomorphicHermiteSum n hn S c (permute σ z)) =
      fun z ↦ permutationSign σ * finiteZeroAntiholomorphicHermiteSum n hn S c z := by
    apply continuous_eq_of_ae_eq_complexGaussian hn
    · have hc : Continuous (finiteZeroAntiholomorphicHermiteSum n hn S c) := by
        convert MvPolynomial.continuous_eval
          (finiteZeroAntiholomorphicHermitePolynomial n S c) using 1
        funext z
        exact (eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z).symm
      apply hc.comp
      exact continuous_pi (fun i ↦ continuous_apply (σ i))
    · have hc : Continuous (finiteZeroAntiholomorphicHermiteSum n hn S c) := by
        convert MvPolynomial.continuous_eval
          (finiteZeroAntiholomorphicHermitePolynomial n S c) using 1
        funext z
        exact (eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z).symm
      exact continuous_const.mul hc
    have hLp := hAlt σ
    have hclass :
        (gaussianPermutationL2 σ (finiteZeroHermiteL2 n hn S c) :
          Configuration n → ℂ) =ᵐ[complexGaussianMeasure n]
        (permutationSign σ • finiteZeroHermiteL2 n hn S c :
          Configuration n → ℂ) := by
      rw [hLp]
      exact Lp.coeFn_smul _ _
    have hcoe := finiteZeroHermiteL2_coeFn n hn S c
    have hcomp := (gaussian_measurePreserving_permute σ).quasiMeasurePreserving.ae_eq_comp hcoe
    filter_upwards [hclass, Lp.coeFn_compMeasurePreserving (finiteZeroHermiteL2 n hn S c)
        (gaussian_measurePreserving_permute σ), hcomp, hcoe] with
        z hpoint hpull hsrc htgt
    rw [show (gaussianPermutationL2 σ (finiteZeroHermiteL2 n hn S c)) z =
      finiteZeroHermiteL2 n hn S c (permute σ z) by exact hpull] at hpoint
    simp only [Pi.smul_apply, smul_eq_mul] at hpoint
    change finiteZeroHermiteL2 n hn S c (permute σ z) =
      finiteZeroAntiholomorphicHermiteSum n hn S c (permute σ z) at hsrc
    change finiteZeroHermiteL2 n hn S c (permute σ z) =
      permutationSign σ * finiteZeroHermiteL2 n hn S c z at hpoint
    rw [hsrc, htgt] at hpoint
    exact hpoint
  exact fun z ↦ congrFun heq z


/-- Every nonzero vector of the actual closed homogeneous quotient space is
itself a finite homogeneous quotient, without a polynomial assumption. -/
theorem ginibre_holomorphic_phase_nonzero_isFinite {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hhol : h ∈ ginibreHolomorphicAmbientClosedSpan n hn)
    (hchar : h ∈ ginibreHolomorphicPhaseDegree n r hn) (hne : h ≠ 0) :
    IsFiniteHomogeneousQuotientVector hn r h := by
  obtain ⟨s, hs, hsv⟩ := hhol
  change s.val = h at hsv
  have hg0 : normalizedVandermondeL2 n hn h ∈ hermiteAntiDegreeClosedSpan n hn 0 := by
    have hmap : vandermondeSymmetricAlternatingEquiv n hn s ∈
        gaussianAlternatingZeroModeClosedSpan n hn := by
      change vandermondeSymmetricAlternatingEquiv n hn s ∈
        (gaussianAlternatingZeroModeClosedSpan n hn).toSubmodule
      rw [← map_ginibreSymmetricHolomorphicPolynomialClosedSpan]
      exact ⟨s, hs, rfl⟩
    have hz := gaussianAlternatingZeroModeClosedSpan_le_hermiteZeroMode n hn hmap
    change normalizedVandermondeL2 n hn s.val ∈ hermiteAntiDegreeClosedSpan n hn 0 at hz
    rwa [hsv] at hz
  have hphase : ∀ (u : ℂ) (hu : ‖u‖ = 1),
      gaussianGlobalPhaseL2 hn u hu (normalizedVandermondeL2 n hn h) =
        u ^ (vandermondeDegree n + r) • normalizedVandermondeL2 n hn h := by
    have hx := hchar
    simpa using gaussianGlobalPhaseL2_normalizedVandermonde_character (r := r) (s := 0) hn h
      (by intro u hu; simpa using hx u hu)
  obtain ⟨S, c, hf, hd⟩ := gaussian_holomorphic_phase_finiteZero_reconstruction hn _ hg0 hphase
  have hAlt : finiteZeroHermiteL2 n hn S c ∈ gaussianAlternatingL2 n := by
    rw [hf, ← hsv]
    exact normalizedVandermondeL2_mem_gaussianAlternating hn s
  have hPalt := finiteZeroHermiteL2_alternating_polynomial hn S c hAlt
  have hPne : finiteZeroAntiholomorphicHermitePolynomial n S c ≠ 0 := by
    intro hP
    have hf0 : finiteZeroHermiteL2 n hn S c = 0 := by
      apply Lp.ext
      filter_upwards [finiteZeroHermiteL2_coeFn n hn S c,
        Lp.coeFn_zero ℂ 2 (complexGaussianMeasure n)] with z hz hzero
      rw [hz, hzero]
      rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z, hP]
      simp
    apply hne
    apply (normalizedVandermondeL2 n hn).injective
    rw [← hf, hf0, map_zero]
  obtain ⟨Q, hQsym, hfactor, hle, hQphase⟩ :=
    homogeneous_alternating_polynomial_division
      (isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree S c hd) hPalt hPne
  have hsEq : finiteHomogeneousQuotientL2 hn S c hAlt = s := by
    apply (vandermondeSymmetricAlternatingEquiv n hn).injective
    rw [finiteHomogeneousQuotientL2, LinearIsometryEquiv.apply_symm_apply]
    apply Subtype.ext
    change finiteZeroHermiteL2 n hn S c = normalizedVandermondeL2 n hn s.val
    rw [hsv]
    exact hf
  refine ⟨S, c, hAlt, Q, hd, hPalt, hPne, hfactor, ?_, ?_, ?_⟩
  · intro z
    rw [← eval_finiteZeroAntiholomorphicHermitePolynomial n hn S c z,
      hfactor, map_mul, eval_polynomialVandermonde]
  · simpa using hQphase
  · rw [hsEq]
    exact hsv.symm

/-- Nonzero vectors of the entire closed homogeneous quotient degree space
are genuine finite homogeneous quotients. -/
theorem ginibre_quotientDegreeClosedSpan_nonzero_isFinite {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : h ∈ ginibreFiniteQuotientDegreeClosedSpan n r hn) (hne : h ≠ 0) :
    IsFiniteHomogeneousQuotientVector hn r h :=
  ginibre_holomorphic_phase_nonzero_isFinite hn h
    (ginibreFiniteQuotientDegreeClosedSpan_le_holomorphicAmbient n r hn hh)
    (ginibreFiniteQuotientDegreeClosedSpan_le_phaseDegree n r hn hh) hne

/-- Within the actual holomorphic space, the phase character completely
identifies a closed homogeneous quotient degree. -/
theorem ginibre_holomorphic_phase_mem_quotientDegree {n r : ℕ} (hn : 0 < n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hhol : h ∈ ginibreHolomorphicAmbientClosedSpan n hn)
    (hchar : h ∈ ginibreHolomorphicPhaseDegree n r hn) :
    h ∈ ginibreFiniteQuotientDegreeClosedSpan n r hn := by
  by_cases hz : h = 0
  · rw [hz]; exact Submodule.zero_mem _
  · apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    exact ginibre_holomorphic_phase_nonzero_isFinite hn h hhol hchar hz

end
end GinibrePoincare
