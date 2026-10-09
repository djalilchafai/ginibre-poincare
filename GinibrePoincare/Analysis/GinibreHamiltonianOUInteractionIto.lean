module

public import GinibrePoincare.Analysis.GinibreHamiltonianInteractionPotential
public import GinibrePoincare.Analysis.GinibreHamiltonianOUCompactStoppedSelection
public import GinibrePoincare.Analysis.GinibreStochasticCompactItoIntegral

@[expose] public section

/-! A genuine original-Brownian compact stopped reference OU process and its
interaction-potential Itô martingale, with all local analytic facts derived. -/
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

theorem ginibreHamiltonianOU_interaction_ito_exists {Ω : Type*} [MeasurableSpace Ω]
    (n : ℕ) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z) :
    ∃ T : ℝ≥0, 0 < T ∧ ∃ K : Set (Configuration n), IsCompact K ∧
      (∀ x ∈ K, CollisionFree x) ∧ ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, Y t ω ∈ K) ∧
      (∀ ω, Y 0 ω = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < θ ω ∧ θ ω ≤ T) ∧
      (∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*(α : ℝ)/(n : ℝ)) • Y s.toNNReal ω) ∧
      ∃ J : ℝ≥0 → Ω → ℝ,
      Martingale J (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)) P ∧
      (∀ ω, Continuous (fun t => J t ω)) ∧ (∀ t, MemLp (J t) 2 P) ∧
      J 0 =ᵐ[P] (fun _ => 0) ∧
      (∀ t ≤ T, TendstoInMeasure P
        (ginibreConfigurationBrownianGradientSum n B α Y (ginibreInteractionPotential n) t) atTop (J t)) ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω,
        ginibreInteractionPotential n (Y t ω)-ginibreInteractionPotential n z-
          ((2*(α : ℝ)/(n : ℝ))*(2*vandermondeDegree n : ℕ))*(t : ℝ) = J t ω := by
  obtain ⟨τ, hτ, K, hK, hKCF, X, θ, hXmeas, hX0, hRange, hAdapt, hStop, hθ, hEq⟩ :=
    ginibreHamiltonianOU_compact_stopped_local_solution_selection n B P hB α z hz
  let T : ℝ≥0 := τ.toNNReal
  let Y : ℝ≥0 → Ω → Configuration n := fun t ω => X ω (projIcc 0 τ hτ.le (t : ℝ))
  have hY0 (ω : Ω) : Y 0 ω = z := by simpa [Y] using hX0 ω
  have hYC (ω : Ω) : Continuous (fun t => Y t ω) :=
    (X ω).continuous.comp ((continuous_projIcc : Continuous (projIcc 0 τ hτ.le)).comp NNReal.continuous_coe)
  have hYR (t : ℝ≥0) (ω : Ω) : Y t ω ∈ K := hRange ω _
  have hθT (ω : Ω) : θ ω ≤ T := by
    have hh := Real.toNNReal_le_toNNReal (hθ ω).2
    simpa [T] using hh
  let b : ℝ → Ω → Configuration n := fun s ω => (-2*(α : ℝ)/(n : ℝ)) • Y s.toNNReal ω
  have hb (ω : Ω) : Continuous (fun s => b s ω) := by
    exact ((hYC ω).comp continuous_real_toNNReal).const_smul (-2*(α : ℝ)/(n : ℝ))
  obtain ⟨R, hR, hRB⟩ := hK.isBounded.exists_pos_norm_le
  let M := |(-2*(α : ℝ)/(n : ℝ))| * R
  have hM : 0 ≤ M := mul_nonneg (abs_nonneg _) hR.le
  have hbound : ∀ s ∈ Icc (0 : ℝ) T, ∀ ω, ‖b s ω‖ ≤ M := by
    intro s hs ω
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hRB _ (hYR _ _)) (abs_nonneg _)
  have hV : ContDiffOn ℝ 2 (ginibreInteractionPotential n) {x | CollisionFree x} :=
    fun x hx => ((ginibreInteractionPotential_contDiffAt n x hx).of_le
      (by exact WithTop.coe_le_coe.mpr (show (2 : ENat) ≤ ⊤ from le_top))).contDiffWithinAt
  have hθm : Measurable θ := by
    have hm : Measurable (fun ω => (θ ω : WithTop ℝ≥0))  := hStop.measurable.mono hStop.measurableSpace_le le_rfl
    have hh := ENNReal.measurable_toNNReal.comp hm
    simpa [Function.comp_def] using hh
  have hVEq : ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
      ∫ s in (0 : ℝ)..t, b s ω := by
    filter_upwards [hEq] with ω hω
    intro t ht
    have htτ : (t : ℝ) ≤ τ := (show (t : ℝ) ≤ (θ ω : ℝ) by exact_mod_cast ht).trans (hθ ω).2
    have h := hω ⟨(t : ℝ), ⟨t.property, htτ⟩⟩ (by exact_mod_cast ht)
    have heval : Y t ω = X ω ⟨(t : ℝ), ⟨t.property, htτ⟩⟩ := by
      apply congrArg (X ω)
      apply Subtype.ext
      simp [Y, projIcc, max_eq_right t.property, min_eq_right htτ]
    rw [heval]
    calc
      _ = z+ginibreConfigurationBrownianNoise n B α ω t+
          ∫ s in (0 : ℝ)..t, (-2*(α : ℝ)/(n : ℝ)) • X ω (projIcc 0 τ hτ.le s) := h
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr
        intro s hs
        have hs0 : 0 ≤ s := by
          have hh : s ∈ Icc (0 : ℝ) (t : ℝ) := by simpa only [uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
          exact hh.1
        dsimp [b, Y]
        rw [max_eq_left hs0]
  have hVol : ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = Y 0 ω+
      (ginibreConfigurationBrownianNoise n B α ω t-ginibreConfigurationBrownianNoise n B α ω 0)+
      ∫ s in (0 : ℝ)..t, b s ω := by
    filter_upwards [hVEq, ginibreConfigurationBrownianNoise_actual n B P hB α] with ω hω hNoise
    intro t ht
    rw [hY0, hNoise.2, sub_zero]
    exact hω t ht
  obtain ⟨J, hJM, hJC, hJL, hJ0, hLimit, hIto⟩ :=
    ginibreCompactVolterra_continuous_ito_integral_exists n B P hB hind α Y hAdapt hYC
      (ginibreInteractionPotential n) {x | CollisionFree x} K (isOpen_collisionFree n) hV hK hKCF hYR
      T b hb M hM hbound θ hθm hθT hVol
  refine ⟨T, Real.toNNReal_pos.mpr hτ, K, hK, hKCF, Y, hYC, hYR, hY0, hAdapt, θ, hStop,
    fun ω => ⟨(hθ ω).1, hθT ω⟩, hVEq, J, hJM, hJC, hJL, hJ0, hLimit,?_⟩
  filter_upwards [hIto] with ω hω
  intro t ht
  have h := hω t ht
  unfold ginibreConfigurationTestCompensator at h
  have hL : (∫ s in (0 : ℝ)..t, configurationLaplacian (ginibreInteractionPotential n) (Y s.toNNReal ω)) = 0 := by
    simp_rw [ginibreInteractionPotential_laplacian _ (hKCF _ (hYR _ _))]
    simp
  have hD : (∫ s in (0 : ℝ)..t, fderiv ℝ (ginibreInteractionPotential n) (Y s.toNNReal ω) (b s ω)) =
      ((2*(α : ℝ)/(n : ℝ))*(2*vandermondeDegree n : ℕ))*(t : ℝ) := by
    have he (s : ℝ) : fderiv ℝ (ginibreInteractionPotential n) (Y s.toNNReal ω) (b s ω) =
        ((2*(α : ℝ)/(n : ℝ))*(2*vandermondeDegree n : ℕ)) := by
      have hg := ginibreInteractionPotential_ou_generator (α : ℝ) (Y s.toNNReal ω) (hKCF _ (hYR _ _))
      rw [ginibreInteractionPotential_laplacian _ (hKCF _ (hYR _ _)), mul_zero, add_zero] at hg
      exact hg
    simp_rw [he]
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
    ring
  simpa [hY0, hL, hD] using h

#print axioms ginibreHamiltonianOU_interaction_ito_exists
end
end GinibrePoincare
