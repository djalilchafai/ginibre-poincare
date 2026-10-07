module

public import GinibrePoincare.Analysis.GinibreEqualityConjugatePolynomialDegree
public import GinibrePoincare.Analysis.GinibreConjugationGeometry

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite
set_option maxHeartbeats 600000

/-- Every genuine finite homogeneous quotient has a nonzero conjugate mode
at its own degree: any finite conjugate support bound is at least that degree. -/
theorem ginibreEquality_finite_quotient_conjugate_degree_bound {n : ℕ} (hn : 0<n)
    (r : ℕ) (h : Lp ℂ 2 (ginibreMeasure n)) (hh : IsFiniteHomogeneousQuotientVector hn r h)
    (b : HermiteMultiIndex n →₀ ℂ) (K : ℕ)
    (hb : ∀ pq ∈ b.support,totalAntiDegree pq ≤ K)
    (hfinite : normalizedVandermondeL2 n hn (star h) = finiteHermiteCombination n hn b) :
    r ≤ K := by
  rcases hh with ⟨S,c,hAlt,Q,hdegree,hpolyAlt,hne,hfactor,hsum,hphase,rfl⟩
  have hhom : MvPolynomial.IsHomogeneous
      (finiteZeroAntiholomorphicHermitePolynomial n S c) (vandermondeDegree n+r) :=
    by
      apply isHomogeneous_finiteZeroAntiholomorphicHermitePolynomial_of_degree
      exact hdegree
  have hQne : Q≠0 := by
    intro hz
    rw [hz,mul_zero] at hfactor
    exact hne hfactor
  have hdegP := hhom.totalDegree hne
  have hdegV := (isHomogeneous_polynomialVandermonde n).totalDegree (polynomialVandermonde_ne_zero n)
  have hdeg := MvPolynomial.totalDegree_mul_of_isDomain (polynomialVandermonde_ne_zero n) hQne
  rw [←hfactor,hdegP,hdegV] at hdeg
  have hbQ := ginibreEquality_conjugate_polynomial_degree_bound hn _ Q
    (finiteHomogeneousQuotientL2_coeFn hn S c hAlt Q hsum) b K hb hfinite
  omega

end GinibrePoincare
