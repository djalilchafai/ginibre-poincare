module

public import GinibrePoincare.Analysis.GinibreValueTruncationWeakChain
public import GinibrePoincare.Analysis.RadialBoundedWeakSobolevApproximation
public import GinibrePoincare.Analysis.GinibreRadialWeakSobolevApproximation

@[expose] public section

/-! # Full reverse radial weak Sobolev approximation

Concrete nonlinear weak truncations remove the boundedness restriction. Every
independent radial weak pair belongs to the original radial smooth completion.
Closedness of the independently radial value class is a separate obligation
for the equality of the two domains.
-/
open MeasureTheory Filter
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

/-- Concrete bounded weak value truncations converge in the actual full
value-gradient Ginibre L² norm. -/
def ginibreWeakValueTruncation (n : ℕ) (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) (m : ℕ) :
    Lp ℝ 2 (ginibreMeasure n) × Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n) :=
  ((ginibreValueTruncation_memLp n m u (Lp.memLp u)).toLp
      (fun z => sobolevValueTruncation m (u z)),
    (ginibreValueTruncation_vector_memLp n m u (Lp.aestronglyMeasurable u) g (Lp.memLp g)).toLp
      (fun z => deriv (sobolevValueTruncation m) (u z) • g z))

theorem ginibreWeakValueTruncation_distributional (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) (m : ℕ) :
    IsGinibreDistributionalGradient n (ginibreWeakValueTruncation n u g m).1
      (ginibreWeakValueTruncation n u g m).2 :=
  ginibreValueTruncation_distributional n hn m u g hg

theorem ginibreWeakValueTruncation_tendsto (n : ℕ)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :
    Tendsto (ginibreWeakValueTruncation n u g) atTop (𝓝 (u, g)) :=
  (ginibreValueTruncation_L2_tendsto n u).prodMk_nhds
    (ginibreValueTruncation_vector_L2_tendsto n u g)

/-- Every independent radial weak pair admits genuine smooth radial core
approximation, without boundedness, support or entropy assumptions. -/
theorem radial_weak_mem_sobolevClosure (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g)
    (hr : IsGinibreRadialL2Value n u) : (u, g) ∈ radialSobolevClosure n := by
  obtain ⟨f, hs, hfr, hf⟩ := hr
  have hm (m : ℕ) : ginibreWeakValueTruncation n u g m ∈ radialSobolevClosure n := by
    refine radial_bounded_weak_mem_sobolevClosure n hn _ _
      (ginibreWeakValueTruncation_distributional n hn u g hg m)
      (fun z => sobolevValueTruncation m (f z)) ?_ ?_ ?_
      (2 * ((m : ℝ) + 1)) (by positivity) ?_
    · exact (ginibreValueTruncation_memLp n m u (Lp.memLp u)).coeFn_toLp.trans
        (hf.fun_comp (sobolevValueTruncation m))
    · exact ginibreValueTruncation_symmetric n m f hs
    · exact ginibreValueTruncation_radial n m f hfr
    · exact fun z => sobolevValueTruncation_bounded m (f z)
  exact isClosed_closure.mem_of_tendsto (ginibreWeakValueTruncation_tendsto n u g)
    (Eventually.of_forall hm)

/-- Full reverse inclusion of the independently defined radial weak-H¹ graph. -/
theorem ginibreRadialWeakSobolevPairs_subset_sobolevClosure (n : ℕ) (hn : 0 < n) :
    ginibreRadialWeakSobolevPairs n ⊆ radialSobolevClosure n := by
  rintro p ⟨hg, hr⟩
  exact radial_weak_mem_sobolevClosure n hn p.1 p.2 hg hr

/-- Sharp LSI and entropy integrability on the full independently radial weak
Sobolev domain, without a smooth-core or boundedness premise. -/
theorem ginibre_radial_weak_lsi (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) (hr : IsGinibreRadialL2Value n u) :
    Integrable (fun z => u z ^ 2 * Real.log (u z ^ 2)) (ginibreMeasure n) ∧
      ginibreSquareEntropy n u ≤ (1 / (n : ℝ)) * ‖g‖ ^ 2 :=
  radial_sobolev_lsi n hn (u, g) (radial_weak_mem_sobolevClosure n hn u g hg hr)

/-- Genuine radial smooth core sequences converge to every independent radial
weak value-gradient pair. -/
theorem radial_weak_exists_core_sequence (n : ℕ) (hn : 0 < n)
    (u : Lp ℝ 2 (ginibreMeasure n))
    (g : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hg : IsGinibreDistributionalGradient n u g) (hr : IsGinibreRadialL2Value n u) :
    ∃ q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n),
      (∀ m, q m ∈ radialSobolevCorePairs n) ∧ Tendsto q atTop (𝓝 (u, g)) :=
  mem_closure_iff_seq_limit.mp (radial_weak_mem_sobolevClosure n hn u g hg hr)
end
end GinibrePoincare
