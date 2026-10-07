module

public import GinibrePoincare.Analysis.GinibreDrivenPathQuadraticCross
public import GinibrePoincare.Analysis.GinibreStochasticOUPath

@[expose] public section

/-! The actual OU correction contributes zero quadratic variation, pathwise. -/
open MeasureTheory Filter ProbabilityTheory Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000

theorem drivenOUPath_quadratic_variation_noise (κ x : ℝ) (N : ℝ → ℝ)
    (hN : Continuous N) (t : ℝ) (ht : 0 ≤ t) :
    Tendsto (fun n => (∑ i ∈ Finset.range (n+1),
      (drivenOUPath κ x N (ginibreUniformTime t n (i+1))-
        drivenOUPath κ x N (ginibreUniformTime t n i))^2)-
        (∑ i ∈ Finset.range (n+1),
          (N (ginibreUniformTime t n (i+1))-N (ginibreUniformTime t n i))^2))
      atTop (𝓝 0) := by
  have hX := drivenOUPath_continuous κ x N hN
  have hd : Continuous (fun s => -κ*drivenOUPath κ x N s) := continuous_const.mul hX
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc 0 t) hd.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 ⟨le_rfl, ht⟩)
  have hLip : LipschitzOnWith ⟨C, hC0⟩ (drivenOUCorrection κ x N) (Icc 0 t) :=
    (convex_Icc (0 : ℝ) t).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun s hs => (drivenOUCorrection_hasDerivAt κ x N hN s).hasDerivWithinAt)
      (fun s hs => by exact_mod_cast (show ‖-κ • drivenOUPath κ x N s‖ ≤ C by simpa only [smul_eq_mul] using hC s hs))
  have hAc : Continuous (drivenOUCorrection κ x N) :=
    continuous_iff_continuousAt.mpr fun s => (drivenOUCorrection_hasDerivAt κ x N hN s).continuousAt
  have h := ginibreUniformQuadraticVariation_add_lipschitz (drivenOUCorrection κ x N) N t ht ⟨C,hC0⟩ hLip hAc hN
  simpa only [Pi.add_apply, drivenOUPath, add_comm] using h

theorem ginibreBrownianOU_quadratic_variation_noise {Ω : Type*} [MeasurableSpace Ω]
    (B : ℝ≥0 → Ω → ℝ) (P : Measure Ω) (hB : IsBrownianReal B P)
    (κ σ x t : ℝ) (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, Tendsto (fun n => (∑ i ∈ Finset.range (n+1),
      (ginibreBrownianOU B κ σ x (ginibreUniformTime t n (i+1)) ω-
        ginibreBrownianOU B κ σ x (ginibreUniformTime t n i) ω)^2)-
        (∑ i ∈ Finset.range (n+1),
          (ginibreBrownianNoise B σ ω (ginibreUniformTime t n (i+1))-
            ginibreBrownianNoise B σ ω (ginibreUniformTime t n i))^2)) atTop (𝓝 0) := by
  filter_upwards [hB.cont] with ω hcont
  exact drivenOUPath_quadratic_variation_noise κ x (ginibreBrownianNoise B σ ω)
    (continuous_const.mul (hcont.comp continuous_real_toNNReal)) t ht

end
end GinibrePoincare
