module

public import GinibrePoincare.Analysis.GinibreStochasticContinuousNoisePath

@[expose] public section

/-! A causal continuous clipping map into the actual local-flow noise domain. -/
open Set
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def drivenNoiseClip (r : ℝ) (x : E) : E := (r / max r ‖x‖) • x

theorem drivenNoiseClip_continuous (r : ℝ) (hr : 0 < r) : Continuous (drivenNoiseClip (E := E) r) := by
  exact (continuous_const.div (continuous_const.max continuous_norm)
    (fun x => ne_of_gt (hr.trans_le (le_max_left _ _)))).smul continuous_id

theorem drivenNoiseClip_norm_le (r : ℝ) (hr : 0 < r) (x : E) : ‖drivenNoiseClip r x‖ ≤ r := by
  have hd : 0 < max r ‖x‖ := hr.trans_le (le_max_left _ _)
  rw [drivenNoiseClip,norm_smul,Real.norm_of_nonneg (div_nonneg hr.le hd.le)]
  calc
    _ ≤ (r/max r ‖x‖)*max r ‖x‖ := mul_le_mul_of_nonneg_left (le_max_right _ _) (div_nonneg hr.le hd.le)
    _ = r := div_mul_cancel₀ _ hd.ne'

theorem drivenNoiseClip_eq (r : ℝ) (hr : 0 < r) (x : E) (hx : ‖x‖ ≤ r) : drivenNoiseClip r x = x := by
  simp [drivenNoiseClip,max_eq_left hx,div_self hr.ne']

def drivenNoiseClipPath (r : ℝ) (hr : 0 < r) (N : C(Icc (-1 : ℝ) 1,E)) : C(Icc (-1 : ℝ) 1,E) :=
  ⟨fun t => drivenNoiseClip r (N t-N ⟨0,by norm_num⟩),
    (drivenNoiseClip_continuous r hr).comp (N.continuous.sub continuous_const)⟩

theorem drivenNoiseClipPath_continuous (r : ℝ) (hr : 0 < r) : Continuous (drivenNoiseClipPath (E := E) r hr) := by
  let c : C(E,E) := ⟨drivenNoiseClip r,drivenNoiseClip_continuous r hr⟩
  have hSub : Continuous (fun N : C(Icc (-1 : ℝ) 1,E) => N-ContinuousMap.const _ (N ⟨0,by norm_num⟩)) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_eval.sub ((continuous_eval_const _).comp continuous_fst)
  exact c.continuous_postcomp.comp hSub

theorem drivenNoiseClipPath_zero (r : ℝ) (hr : 0 < r) (N : C(Icc (-1 : ℝ) 1,E)) :
    drivenNoiseClipPath r hr N ⟨0,by norm_num⟩ = 0 := by
  simp [drivenNoiseClipPath,drivenNoiseClip]

theorem drivenNoiseClipPath_norm_le (r : ℝ) (hr : 0 < r) (N : C(Icc (-1 : ℝ) 1,E)) :
    ‖drivenNoiseClipPath r hr N‖ ≤ r := by
  apply (ContinuousMap.norm_le _ hr.le).mpr
  intro t
  exact drivenNoiseClip_norm_le r hr _

end
end GinibrePoincare
