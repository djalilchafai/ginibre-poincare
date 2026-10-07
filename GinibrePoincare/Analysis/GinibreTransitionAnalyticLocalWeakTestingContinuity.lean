module

public import GinibrePoincare.Analysis.GinibreTransitionAnalyticLocalWeakTestingApproximation

@[expose] public section

open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1200000

/-- Compact weak equations extend to genuine Sobolev limits by continuity
of the actual weighted L² pairings. -/
theorem ginibreLocalWeak_pairing_limit {n : ℕ}
    (A C H : Lp ℝ 2 (ginibreMeasure n))
    (B : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (ℓ c : ℝ)
    (q : ℕ → Lp ℝ 2 (ginibreMeasure n) ×
      Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (v : Lp ℝ 2 (ginibreMeasure n))
    (G : Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n))
    (hq : Tendsto q atTop (𝓝 (v,G)))
    (heq : ∀ m, ℓ*inner ℝ A (q m).1+c*inner ℝ B (q m).2+
      c*inner ℝ H (q m).1=inner ℝ C (q m).1) :
    ℓ*inner ℝ A v+c*inner ℝ B G+c*inner ℝ H v=inner ℝ C v := by
  have hA : Tendsto (fun m => inner ℝ A (q m).1) atTop (𝓝 (inner ℝ A v)) :=
    tendsto_const_nhds.inner (hq.fst_nhds)
  have hB : Tendsto (fun m => inner ℝ B (q m).2) atTop (𝓝 (inner ℝ B G)) :=
    tendsto_const_nhds.inner (hq.snd_nhds)
  have hH : Tendsto (fun m => inner ℝ H (q m).1) atTop (𝓝 (inner ℝ H v)) :=
    tendsto_const_nhds.inner (hq.fst_nhds)
  have hl : Tendsto (fun m => ℓ*inner ℝ A (q m).1+c*inner ℝ B (q m).2+
      c*inner ℝ H (q m).1) atTop
      (𝓝 (ℓ*inner ℝ A v+c*inner ℝ B G+c*inner ℝ H v)) := ((tendsto_const_nhds.mul hA).add (tendsto_const_nhds.mul hB)).add
    (tendsto_const_nhds.mul hH)
  have hr : Tendsto (fun m => inner ℝ C (q m).1) atTop (𝓝 (inner ℝ C v)) :=
    tendsto_const_nhds.inner (hq.fst_nhds)
  exact tendsto_nhds_unique (hl.congr' (Eventually.of_forall heq)) hr

#print axioms ginibreLocalWeak_pairing_limit
end
end GinibrePoincare
