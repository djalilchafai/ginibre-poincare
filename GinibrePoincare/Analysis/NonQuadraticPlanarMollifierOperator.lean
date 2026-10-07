module

public import GinibrePoincare.Analysis.NonQuadraticPlanarL2Mollification
public import GinibrePoincare.Analysis.NonQuadraticStrongOperatorLimit

@[expose] public section

/-! # Actual complex-linear planar mollifier operators -/
open MeasureTheory Filter
open scoped Topology ENNReal
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false

theorem planarL2Translate_complex_smul (y c : ℂ) (u : Lp ℂ 2 (volume : Measure ℂ)) :
    planarL2Translate y (c • u) = c • planarL2Translate y u := by
  apply Lp.ext
  have he := (eventually_add_right_iff (volume : Measure ℂ) (-y)).mpr (Lp.coeFn_smul c u)
  filter_upwards [planarL2Translate_ae y (c • u), Lp.coeFn_smul c (planarL2Translate y u),
    planarL2Translate_ae y u, he] with x hx hs ht he
  change (c • u) (x-y) = c • u (x-y) at he
  rw [hx, hs]
  change (c • u) (x-y) = c • (planarL2Translate y u) x
  rw [ht, he]

def planarMollifierLinear (φ : ContDiffBump (0 : ℂ)) :
    Lp ℂ 2 (volume : Measure ℂ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℂ) where
  toFun := planarL2BumpAverage φ
  map_add' u v := by
    unfold planarL2BumpAverage planarL2Translate
    simp only [DomAddAct.vadd_Lp_add, smul_add]
    exact integral_add (integrable_planarL2BumpIntegrand φ u) (integrable_planarL2BumpIntegrand φ v)
  map_smul' c u := by
    change planarL2BumpAverage φ (c • u) = c • planarL2BumpAverage φ u
    unfold planarL2BumpAverage
    simp only [planarL2Translate_complex_smul, smul_comm (φ.normed volume _) c]
    exact integral_smul c _

/-- Genuine complex-linear convolution averaging on the whole planar L² space. -/
def planarMollifierOperator (φ : ContDiffBump (0 : ℂ)) :
    Lp ℂ 2 (volume : Measure ℂ) →L[ℂ] Lp ℂ 2 (volume : Measure ℂ) :=
  (planarMollifierLinear φ).mkContinuous 1 (fun u => by
    simpa only [one_mul, planarMollifierLinear, LinearMap.coe_mk, AddHom.coe_mk] using norm_planarL2BumpAverage_le φ u)

theorem planarMollifierOperator_norm_le (φ : ContDiffBump (0 : ℂ)) :
    ‖planarMollifierOperator φ‖ ≤ 1 :=
  LinearMap.mkContinuous_norm_le _ (by norm_num) _

theorem planarMollifierOperator_tendsto (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0)) (u : Lp ℂ 2 (volume : Measure ℂ)) :
    Tendsto (fun m => planarMollifierOperator (φ m) u) atTop (𝓝 u) :=
  planarL2BumpAverage_tendsto φ hφ u
/-- Actual scalar mollifiers converge strongly in the left coordinate on
all complex-valued L² functions of two planar variables. -/
theorem planarProductLeftMollifier_tendsto (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp ℂ 2 ((volume : Measure ℂ).prod volume)) :
    Tendsto (fun m => l2ProductLeftOperator (ν := (volume : Measure ℂ))
      (planarMollifierOperator (φ m)) u) atTop (𝓝 u) := by
  apply productL2_left_strong_limit atTop _ 1 _ _ u
  · intro m
    exact_mod_cast planarMollifierOperator_norm_le (φ m)
  · exact planarMollifierOperator_tendsto φ hφ

/-- Actual scalar mollifiers converge strongly in the right coordinate on
all complex-valued L² functions of two planar variables. -/
theorem planarProductRightMollifier_tendsto (φ : ℕ → ContDiffBump (0 : ℂ))
    (hφ : Tendsto (fun m => (φ m).rOut) atTop (𝓝 0))
    (u : Lp ℂ 2 ((volume : Measure ℂ).prod volume)) :
    Tendsto (fun m => l2ProductRightOperator (μ := (volume : Measure ℂ))
      (planarMollifierOperator (φ m)) u) atTop (𝓝 u) := by
  apply productL2_right_strong_limit atTop _ 1 _ _ u
  · intro m
    exact_mod_cast planarMollifierOperator_norm_le (φ m)
  · exact planarMollifierOperator_tendsto φ hφ

end
end GinibrePoincare
