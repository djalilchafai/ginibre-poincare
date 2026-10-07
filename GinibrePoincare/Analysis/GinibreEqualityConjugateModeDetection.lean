module

public import GinibrePoincare.Analysis.GinibreEqualityFiniteConjugateDegree
public import GinibrePoincare.Analysis.GaussianHermitePhaseSpectrum
public import GinibrePoincare.Analysis.GaussianVandermondePhase

@[expose] public section

noncomputable section
namespace GinibrePoincare
open MeasureTheory ComplexHermite
open scoped ComplexConjugate
set_option maxHeartbeats 600000

/-- Vanishing actual high anti-degree projections implies vanishing every
corresponding Hilbert-basis coefficient. -/
theorem gaussianHermiteCoefficient_eq_zero_of_high_projections {n : ℕ} (hn : 0<n)
    (x : Lp ℂ 2 (complexGaussianMeasure n)) (K : ℕ)
    (hx : ∀ d : ℕ,K<d → hermiteAntiDegreeProjection n hn d x=0)
    (pq : HermiteMultiIndex n) (hpq : K<totalAntiDegree pq) :
    gaussianHermiteCoefficient hn x pq=0 := by
  have hi := inner_basis_gaussianHermiteMode hn x (totalAntiDegree pq) pq
  rw [if_pos rfl,gaussianHermiteMode_eq_antiDegreeProjection,hx _ hpq,inner_zero_right] at hi
  exact hi.symm

/-- Bounded conjugate anti modes of a genuine homogeneous phase vector
are an actual finite Gaussian polynomial, with no polynomial assumption. -/
theorem ginibreEquality_phase_conjugate_low_modes_finite {n r : ℕ} (hn : 0<n)
    (h : Lp ℂ 2 (ginibreMeasure n))
    (hphase : ∀ (u : ℂ) (hu : ‖u‖=1),ginibreGlobalPhaseL2 hn u hu h=u^r•h)
    (K : ℕ)
    (hanti : ∀ d : ℕ,K<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star h))=0) :
    ∃ b : HermiteMultiIndex n →₀ ℂ,
      normalizedVandermondeL2 n hn (star h)=finiteHermiteCombination n hn b ∧
      ∀ pq ∈ b.support,totalAntiDegree pq≤K := by
  have hc : ∀ (u : ℂ) (hu : ‖u‖=1),ginibreGlobalPhaseL2 hn u hu (star h)=
      (u^0*(conj u)^r)•star h := by
    intro u hu
    simpa using ginibreGlobalPhaseL2_star_eigen hn h hphase u hu
  have hG := gaussianGlobalPhaseL2_normalizedVandermonde_character hn (star h) hc
  obtain ⟨b,hb,hs⟩ := gaussian_mixed_phase_finite_reconstruction hn
    (normalizedVandermondeL2 n hn (star h)) (by simpa using hG)
    (gaussianHermiteCoefficient_eq_zero_of_high_projections hn _ K hanti)
  exact ⟨b,hb.symm,fun pq hpq => (hs pq hpq).1⟩

/-- Actual finite homogeneous quotient degree is detected by its conjugate
Gaussian projections. Thus degrees above K cannot have only anti modes ≤K. -/
theorem ginibreEquality_finite_quotient_degree_le_of_conjugate_modes {n : ℕ} (hn : 0<n)
    (r : ℕ) (h : Lp ℂ 2 (ginibreMeasure n)) (hh : IsFiniteHomogeneousQuotientVector hn r h)
    (K : ℕ)
    (hanti : ∀ d : ℕ,K<d → hermiteAntiDegreeProjection n hn d
      (normalizedVandermondeL2 n hn (star h))=0) : r≤K := by
  have hp : ∀ (u : ℂ) (hu : ‖u‖=1),ginibreGlobalPhaseL2 hn u hu h=u^r•h := by
    rcases hh with ⟨S,c,hAlt,Q,hdegree,hpolyAlt,hne,hfactor,hsum,hphase,rfl⟩
    exact finiteHomogeneousQuotientL2_mem_phaseDegree hn S c hAlt Q hsum hphase
  obtain ⟨b,hb,hbs⟩ := ginibreEquality_phase_conjugate_low_modes_finite hn h hp K hanti
  exact ginibreEquality_finite_quotient_conjugate_degree_bound hn r h hh b K hbs hb

end GinibrePoincare
