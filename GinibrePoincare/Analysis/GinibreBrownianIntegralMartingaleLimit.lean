module

public import GinibrePoincare.Analysis.GinibreBrownianIntegralL2Completion

@[expose] public section

/-! Genuine strong L² limits preserve the martingale identity. -/
open MeasureTheory Filter
open scoped Topology
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem realMartingale_of_actual_L2_limits {Ω τ : Type*} [MeasurableSpace Ω] [Preorder τ]
    (P : Measure Ω) [IsFiniteMeasure P] (ℱ : Filtration τ (inferInstance : MeasurableSpace Ω))
    (S : ℕ → τ → Ω → ℝ) (hS : ∀ n, Martingale (S n) ℱ P)
    (hs : ∀ n t, MemLp (S n t) 2 P) (M : τ → Ω → ℝ)
    (hM : StronglyAdapted ℱ M) (hm : ∀ t, MemLp (M t) 2 P)
    (hlim : ∀ t, Tendsto (fun n => (hs n t).toLp (S n t)) atTop (𝓝 ((hm t).toLp (M t)))) :
    Martingale M ℱ P := by
  refine ⟨hM,?_⟩
  intro s t hst
  let A := fun u : Lp ℝ 2 P => (condExpL2 ℝ ℝ (ℱ.le s) u : Lp ℝ 2 P)
  have hA : Continuous A := continuous_subtype_val.comp (condExpL2 ℝ ℝ (ℱ.le s)).continuous
  have he (n : ℕ) : A ((hs n t).toLp (S n t)) = (hs n s).toLp (S n s) := by
    apply Lp.ext
    have hce := (hs n t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le s)
    have hmart := (hS n).condExp_ae_eq hst
    filter_upwards [hce,hmart,(hs n s).coeFn_toLp] with ω hc hb hsω
    exact hc.trans (hb.trans hsω.symm)
  have hleft := hA.tendsto ((hm t).toLp (M t)) |>.comp (hlim t)
  have hright : Tendsto (fun n => A ((hs n t).toLp (S n t))) atTop (𝓝 ((hm s).toLp (M s))) := by
    simpa only [he] using hlim s
  have hid : A ((hm t).toLp (M t)) = (hm s).toLp (M s) := tendsto_nhds_unique hleft hright
  have hce := (hm t).condExpL2_ae_eq_condExp (𝕜 := ℝ) (ℱ.le s)
  have hae : (fun ω => A ((hm t).toLp (M t)) ω) =ᵐ[P] M s := by
    rw [hid]
    exact (hm s).coeFn_toLp
  exact hce.symm.trans hae

end
end GinibrePoincare
