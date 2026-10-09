module

public import GinibrePoincare.Analysis.GinibreEqualityConjugateProjection
public import GinibrePoincare.Analysis.HolomorphicQuotientPhaseFinite

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite
set_option maxHeartbeats 600000

/-- Every high quotient degree projection of a positive holomorphic vector
with no high conjugate Gaussian modes vanishes. -/
theorem ginibreEquality_high_quotient_projection_zero {n : ℕ} (hn : 0<n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : h ∈ ginibrePositiveQuotientGradedClosedSpan n hn)
    (hanti : ∀ d : ℕ, 1<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star h))=0)
    (r : ℕ) (hr : 2≤r) :
    (ginibreFiniteQuotientDegreeClosedSpan n r hn).starProjection h=0 := by
  by_contra hne
  let p := (ginibreFiniteQuotientDegreeClosedSpan n r hn).starProjection h
  have hp : IsFiniteHomogeneousQuotientVector hn r p :=
    ginibre_quotientDegreeClosedSpan_nonzero_isFinite hn p
      (Submodule.starProjection_apply_mem _ _) hne
  have ha : ∀ d : ℕ, 1<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star p))=0 := by
    intro d hd
    exact ginibreEquality_conjugate_mode_quotient_projection hn h hh r d (hanti d hd)
  have hl := ginibreEquality_finite_quotient_degree_le_of_conjugate_modes hn r p hp 1 ha
  omega

/-- Complete high-degree elimination on the entire positive holomorphic
closed span, without a finite-polynomial assumption on the vector. -/
theorem ginibreEquality_positive_conjugate_low_modes_mem_first {n : ℕ} (hn : 0<n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hh : h ∈ ginibrePositiveQuotientGradedClosedSpan n hn)
    (hanti : ∀ d : ℕ, 1<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star h))=0) :
    h ∈ ginibreFiniteQuotientDegreeClosedSpan n 1 hn := by
  let P := (ginibreFiniteQuotientDegreeClosedSpan n 1 hn).starProjection
  let x := h-P h
  let S : ClosedSubmodule ℂ (Lp ℂ 2 (ginibreMeasure n)) :=
    ⟨(innerSL ℂ x).ker, (innerSL ℂ x).isClosed_ker⟩
  have hS : ginibrePositiveQuotientGradedClosedSpan n hn ≤ S := by
    apply iSup_le
    intro s f hf
    change inner ℂ x f=0
    by_cases hs : s.val=1
    · exact Submodule.starProjection_inner_eq_zero h f (by simpa [hs] using hf)
    · have hsz : (ginibreFiniteQuotientDegreeClosedSpan n s.val hn).starProjection h=0 :=
        ginibreEquality_high_quotient_projection_zero hn h hh hanti s.val (by omega)
      have hif : inner ℂ h f=0 := by
        simpa only [hsz, sub_zero] using
          Submodule.starProjection_inner_eq_zero h f hf
      have hpf : inner ℂ (P h) f=0 :=
        (ginibreFiniteQuotientDegreeClosedSpan_orthogonal hn (Ne.symm hs)).inner_eq
          (Submodule.starProjection_apply_mem _ _) hf
      change inner ℂ (h-P h) f=0
      rw [inner_sub_left, hif, hpf, sub_self]
  have hxp : x ∈ ginibrePositiveQuotientGradedClosedSpan n hn :=
    (ginibrePositiveQuotientGradedClosedSpan n hn).sub_mem hh
      (ginibreFiniteQuotientDegreeClosedSpan_le_positive n 1 hn (by decide)
        (Submodule.starProjection_apply_mem _ _))
  have hxx : inner ℂ x x=0 := hS hxp
  have hx : x=0 := inner_self_eq_zero.mp hxx
  have hEq : h=P h := sub_eq_zero.mp hx
  rw [hEq]
  exact Submodule.starProjection_apply_mem _ _

end GinibrePoincare
