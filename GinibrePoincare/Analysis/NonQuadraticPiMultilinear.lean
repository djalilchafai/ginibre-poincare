module

public import GinibrePoincare.Analysis.NonQuadraticL2PiProducts
public import Mathlib.Analysis.Normed.Module.Multilinear.Basic

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section
set_option maxHeartbeats 60000
set_option backward.isDefEq.respectTransparency false
variable {m : ℕ} {X : Type*} [MeasurableSpace X]
    (μ : Fin (m+1) → Measure X) [∀ i, SigmaFinite (μ i)]

theorem l2PiProductVector_update_add [DecidableEq (Fin (m+1))] (u : ∀ i, Lp ℂ 2 (μ i)) (i : Fin (m+1))
    (a b : Lp ℂ 2 (μ i)) :
    l2PiProductVector μ (Function.update u i (a+b)) =
      l2PiProductVector μ (Function.update u i a) + l2PiProductVector μ (Function.update u i b) := by
  apply (l2PiCoordinateEquiv μ i).injective
  rw [map_add, l2PiProductVector_split, l2PiProductVector_split, l2PiProductVector_split]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)]
  change l2ProductBilinear (a+b) _ = _
  rw [map_add, LinearMap.add_apply]
  rfl

theorem l2PiProductVector_update_smul [DecidableEq (Fin (m+1))] (u : ∀ i, Lp ℂ 2 (μ i)) (i : Fin (m+1))
    (c : ℂ) (a : Lp ℂ 2 (μ i)) :
    l2PiProductVector μ (Function.update u i (c • a)) =
      c • l2PiProductVector μ (Function.update u i a) := by
  apply (l2PiCoordinateEquiv μ i).injective
  rw [map_smul, l2PiProductVector_split, l2PiProductVector_split]
  simp only [Function.update_self, Function.update_of_ne (Fin.succAbove_ne i _)]
  change l2ProductBilinear (c • a) _ = _
  rw [map_smul, LinearMap.smul_apply]
  rfl

def l2PiProductMultilinear : MultilinearMap ℂ (fun i => Lp ℂ 2 (μ i)) (Lp ℂ 2 (Measure.pi μ)) where
  toFun := l2PiProductVector μ
  map_update_add' u i a b := l2PiProductVector_update_add μ u i a b
  map_update_smul' u i c a := l2PiProductVector_update_smul μ u i c a

def l2PiProductContinuousMultilinear :
    ContinuousMultilinearMap ℂ (fun i => Lp ℂ 2 (μ i)) (Lp ℂ 2 (Measure.pi μ)) :=
  (l2PiProductMultilinear μ).mkContinuous 1 (fun u => by
    change ‖l2PiProductVector μ u‖ ≤ _
    rw [l2PiProductVector_norm]
    simp)
end
end GinibrePoincare
