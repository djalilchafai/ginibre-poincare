module

public import GinibrePoincare.Analysis.GinibreStochasticCenterGlobalNonvanishing
public import GinibrePoincare.Analysis.BrownianOrthogonalGlobalPathElement

@[expose] public section

/-! The genuine center-nonhitting event is Borel in the continuous-path space.
This permits independent random positive initial centers in canonical restarts. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

def ginibrePositiveCenterPaths (n : ℕ) : Set C(ℝ, Configuration n) :=
  {p | ∀ t : ℝ, 0 ≤ t → 0 < ginibreCenterSquared n (p t)}

theorem ginibrePositiveCenterPaths_measurable (n : ℕ) :
    @MeasurableSet C(ℝ, Configuration n) (borel _) (ginibrePositiveCenterPaths n) := by
  letI : MeasurableSpace C(ℝ, Configuration n) := borel _
  letI : BorelSpace C(ℝ, Configuration n) := ⟨rfl⟩
  have he : ginibrePositiveCenterPaths n =
      ⋂ k : ℕ, {p : C(ℝ, Configuration n) | MapsTo p (Icc (0 : ℝ) k)
        {z | 0 < ginibreCenterSquared n z}} := by
    ext p
    simp only [ginibrePositiveCenterPaths, mem_setOf_eq, mem_iInter, MapsTo, mem_Icc]
    constructor
    · intro hp k t ht
      exact hp t ht.1
    · intro hp t ht
      obtain ⟨k, hk⟩ := exists_nat_ge t
      exact hp k ⟨ht, hk⟩
  rw [he]
  apply MeasurableSet.iInter
  intro k
  exact (ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc
    (isOpen_lt continuous_const (contDiff_ginibreCenterSquared n).continuous)).measurableSet

theorem ginibreDrivenGlobalPathElement_center_nonhitting_noise_ae
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 2 ≤ n) (α : ℝ≥0)
    (z : {z : Configuration n // CollisionFree z}) (hc : 0 < ginibreCenterSquared n z.val)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ N ∂P.map (ginibreBrownianFullContinuousNoise n B α),
      ginibreDrivenGlobalPathElement α (z, N) ∈ ginibrePositiveCenterPaths n := by
  have hm := ginibreBrownianFullContinuousNoise_measurable n B P hB α
  have hPath : @Measurable _ C(ℝ, Configuration n) _ (borel _)
      (fun N : GinibreContinuousNoise n => ginibreDrivenGlobalPathElement α (z, N)) :=
    (ginibreDrivenGlobalPathElement_measurable (by omega) α).comp measurable_prodMk_left
  rw [ae_map_iff hm.aemeasurable
    (hPath (ginibrePositiveCenterPaths_measurable n))]
  filter_upwards [ginibreBrownian_center_global_nonvanishing hn α z.val z.property hc B P hB hind,
    ginibreBrownianMaximalLifetime_top_ae (by omega) α z.val z.property B P hB hind]
    with ω hnonzero htop
  intro t ht
  change 0 < ginibreCenterSquared n
    (ginibreDrivenGlobalPathElement α (z, ginibreBrownianFullContinuousNoise n B α ω) t)
  unfold ginibreBrownianMaximalLifetime at htop
  simp only [ginibreDrivenGlobalPathElement, Prod.fst, Prod.snd, dif_pos htop,
    ContinuousMap.coe_mk]
  exact lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm (hnonzero t.toNNReal))

#print axioms ginibrePositiveCenterPaths_measurable
#print axioms ginibreDrivenGlobalPathElement_center_nonhitting_noise_ae
end
end GinibrePoincare
