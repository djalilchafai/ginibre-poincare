module

public import GinibrePoincare.Analysis.BrownianStoppingExitLifetimeStopping
public import GinibrePoincare.Analysis.GinibreHamiltonianMaximalLevel
public import GinibrePoincare.Analysis.GinibreStochasticContinuousStoppingTime

@[expose] public section

/-! Measurable Hamiltonian paths on each alive compact time prefix. -/
open Set MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

 def ginibreBrownianHamiltonianPrefix {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) : C(Icc (0 : ℝ≥0) T, ℝ) :=
  ContinuousMap.mkD (fun t => if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω
    then ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0) 0

 theorem ginibreBrownianHamiltonianPrefix_continuous {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) : Continuous (fun t : Icc (0 : ℝ≥0) T =>
      if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω then
        ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0) := by
  classical
  by_cases hT : (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω
  · simp only [if_pos hT]
    let N := ginibreBrownianFullContinuousNoise n B α ω
    have hc := ginibreDrivenMaximalPath_hamiltonian_continuousOn n α N.val z
    have hg : Continuous (fun t : Icc (0 : ℝ≥0) T => ((t : ℝ≥0) : ℝ)) :=
      NNReal.continuous_coe.comp continuous_subtype_val
    have hm : MapsTo (fun t : Icc (0 : ℝ≥0) T => ((t : ℝ≥0) : ℝ)) univ
        (ginibreDrivenMaximalDomain n α N.val z) := by
      intro t _
      refine ⟨t.val.coe_nonneg, ?_⟩
      rw [ENNReal.ofReal_coe_nnreal]
      exact (ENNReal.coe_le_coe.mpr t.property.2).trans_lt hT
    have hh := hc.comp_continuous hg (fun t => hm (Set.mem_univ t))
    simpa only [ginibreDrivenMaximalPath, ginibreBrownianMaximalProcess,
      Real.toNNReal_coe, Function.comp_def, N] using hh
  · simp only [if_neg hT]
    exact continuous_const

 theorem ginibreBrownianHamiltonianPrefix_apply {Ω : Type*} (n : ℕ) (α : ℝ)
    (z : Configuration n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (ω : Ω) (t : Icc (0 : ℝ≥0) T) :
    ginibreBrownianHamiltonianPrefix n α z B T ω t =
      if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω then
        ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0 := by
  exact ContinuousMap.mkD_apply_of_continuous
    (ginibreBrownianHamiltonianPrefix_continuous n α z B T ω)

 theorem ginibreHamiltonian_measurable (n : ℕ) : Measurable (ginibreHamiltonian n) := by
  exact (measurable_const.mul (contDiff_configurationNormSq (n := n)).continuous.measurable).sub
    (Real.measurable_log.comp (contDiff_vandermondeWeight n).continuous.measurable)

 theorem ginibreBrownianHamiltonianPrefix_measurable {Ω : Type*} [mAmbient : MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (T : ℝ≥0) :
    @Measurable Ω C(Icc (0 : ℝ≥0) T, ℝ)
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T)
      (borel _) (ginibreBrownianHamiltonianPrefix n α z B T) := by
  classical
  letI : Nonempty (Icc (0 : ℝ≥0) T) := ⟨⟨0, by simp⟩⟩
  letI : MeasurableSpace C(Icc (0 : ℝ≥0) T, ℝ) := borel _
  letI : BorelSpace C(Icc (0 : ℝ≥0) T, ℝ) := ⟨rfl⟩
  have hAlive := (ginibreBrownianMaximalLifetime_isStoppingTime hn α z B P hB).measurableSet_gt T
  change @MeasurableSet Ω
    (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T)
    {ω | (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω} at hAlive
  apply ginibre_measurable_continuousMap_of_evaluations
    (mΩ := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T)
  intro t
  have hm := ((ginibreBrownianMaximalProcess_stronglyAdapted hn α z B P hB t).mono
    ((ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)).mono
      t.property.2)).measurable
  have hi : @Measurable Ω ℝ
      (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal) T) _
      (fun ω => if (T : ℝ≥0∞) < ginibreBrownianMaximalLifetime n α z B ω then
        ginibreHamiltonian n (ginibreBrownianMaximalProcess n α z B t ω) else 0) :=
    ((ginibreHamiltonian_measurable n).comp hm).ite hAlive measurable_const
  simpa only [ginibreBrownianHamiltonianPrefix_apply] using hi

end
end GinibrePoincare
