module
public import GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultInterior
public import GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMollifier
public import GinibrePoincare.Analysis.NonQuadraticPiCompactGraphApproximation

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem ordinaryDolbeaultPiMollification_eq {n : ℕ}
    (φ : ContDiffBump (0 : ℂ)) (a : Configuration n → ℂ) :
    ordinaryDolbeaultMollify (fun p => Complex.ofReal (piPlanarBump n φ p)) a =
      piPlanarBump n φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] a := by
  funext p
  unfold ordinaryDolbeaultMollify convolution
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by simp [Complex.real_smul])

theorem ordinaryDolbeaultPiMollification_closed_ball {n : ℕ}
    (α : Fin n → Configuration n → ℂ) (hα : ∀ j, MemLp (α j) 2 volume)
    (x : Configuration n) (R : ℝ)
    (hclosed : ∀ θ : Configuration n → ℂ, ContDiff ℝ ∞ θ → HasCompactSupport θ →
      tsupport θ ⊆ ball x R → ∀ j k,
        (∫ y, dbarComponent θ k y * α j y) = ∫ y, dbarComponent θ j y * α k y)
    (φ : ContDiffBump (0 : ℂ)) (p : Configuration n)
    (hp : φ.rOut + dist p x < R) (j k : Fin n) :
    dbarComponent (piPlanarBump n φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] α j) k p =
      dbarComponent (piPlanarBump n φ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,volume] α k) j p := by
  rw [← ordinaryDolbeaultPiMollification_eq φ (α j),← ordinaryDolbeaultPiMollification_eq φ (α k)]
  exact ordinaryDolbeaultMollify_closed_on (ball x R) α
    (fun t => (hα t).locallyIntegrable (by norm_num)) hclosed _
    (Complex.ofRealCLM.contDiff.comp (dolbeaultPiBump_contDiff n φ))
    ((piPlanarBump_compact n φ).comp_left Complex.ofReal_zero) p
    (dolbeaultBump_translated_tsupport_interior φ x p R hp) j k

#print axioms ordinaryDolbeaultPiMollification_eq
#print axioms ordinaryDolbeaultPiMollification_closed_ball
end
end GinibrePoincare
